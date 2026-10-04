/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.TypeIIGrottoTab

set_option autoImplicit false

/-!
# `M2H.CortoLarge` spined: `eq:corto` (`v = 2`, `S ≥ 10⁵`) from `lem:yutto` + one weight lemma

`M2H.CortoLarge` asks `HC.cortoLHS 2 S ≤ 0.37273` for `S ≥ 10⁵` (`minarcs.tex` 3180-3266). The
whole bookkeeping of Helfgott's proof is PROVED here; what remains is three named links:

```
 corto_split    eq:grotto = ∑_{m ≤ 10⁴} g₂(m)·wt(m, S) + ∑_{s odd} (1/s)∫ tl(uS/s)    EXACT
 main_le        ∑_{m ≤ 10⁴} g₂(m) wt ≤ 0.360577 + 47734020.6/S²   (WeightEM + HC.CortoC0Cited)
 tail_s         one s: (1/s)∫ tl ≤ (log 2/S)(a₁ + a₂) + bC/(2s)
                (HC.YuttoSmallCited on [10001, 10⁶], YuttoMid2 on (10⁶, 10¹⁰), YuttoBig2 above)
 sum2_le        ∑ a₂ over odd s ≤ S/10⁶  (log z ≤ 2(√z − 1), ∑ 1/√(2k+1) ≤ √(2K))
 tel / sum3_le  ∑ 1/(s log²(S/2s)) over odd s ≤ S/10¹⁰, telescoped against 1/log(S/2s)
 cortoLarge_of_links : M2H.CortoLarge                                                  PROVED
   from YuttoMid2, YuttoBig2, WeightEM (links) + HC.YuttoSmallCited, HC.CortoC0Cited (cited)
```

The bound reached is `0.37083` at worst (`S = 10⁶`), against `0.37273`: counting only ODD `s`
(Helfgott does not) frees enough room to take `WeightEM` with error factor `1` instead of the
printed `c_{2,0} = 1/3`.

**Finding (the two `lem:yutto` links).** Their statements are Helfgott's verbatim, but the printed
proof (`minarcs.tex` 3046-3100, identical in the book `typeII.tex` 580-637) does not establish
them. (a) `|g_v(x)| ≤ (2/x)^{1−2ε}F_v(1/2+ε, 1/2+ε)` with `ε = 1/log x` is turned into
`(2/x)·55.768C(1 + log x/2)`, dropping `(x/2)^{2ε} = e^{2 − 2log 2/log x} ≈ 6.7` (no choice of `ε`
recovers more than a factor `≈ 1.45` of it). (b) For `v = 2`, `x ≥ 10¹⁰`, the last step
`25.607/(√x log x) + (1634.34 + 817.168 log x)/x ≤ 0.2046/√x` is false at `x = 10¹⁰`
(left side `1.3165/√x`). With the printed method's honest constants this reduction no longer
closes (the `(10⁶, 10¹⁰)` tail alone then exceeds the `0.0115` of room), so discharging
`YuttoMid2` needs a genuinely better bound on `|g₂|` on `[10⁶, 10¹⁰)` (a `817.168` that may grow
by at most `≈ 1.2×` in this bookkeeping).
-/

namespace Principia.Common.TernaryGoldbach.M2L

open MeasureTheory Set

/-! ## (0) Objects and links -/

/-- `𝟙[⌊uS/s⌋ = m]`. -/
noncomputable def ind (m : ℕ) (S : ℝ) (s : ℕ) (u : ℝ) : ℝ :=
  if ⌊u * S / s⌋₊ = m then 1 else 0

/-- The exact weight of `g₂(m)` in `eq:grotto`: `∑_{s ≤ S odd} (1/s)·|{u ∈ [1/2, 1] : ⌊uS/s⌋ = m}|`
(this is `eq:greco`'s left side, `v = 2`). -/
noncomputable def wt (m : ℕ) (S : ℝ) : ℝ :=
  ∑ s ∈ (Finset.Icc 1 ⌊S⌋₊).filter (fun s => Nat.Coprime s 2),
    1 / (s : ℝ) * ∫ u in (1 / 2 : ℝ)..1, ind m S s u

/-- The part of `g₂` at arguments `≥ C₀ + 1 = 10001`. -/
noncomputable def tl (x : ℝ) : ℝ := if (10001 : ℝ) ≤ x then HC.gYutto 2 x else 0

/-- **Link [YuttoMid2] — `lem:yutto`, `v = 2`, middle range** (`minarcs.tex` 2858-2877):
`|g₂(x)| ≤ (1634.34 + 817.168 log x)/x` for `10⁶ ≤ x < 10¹⁰`. Helfgott's own lemma, stated
verbatim; its printed proof drops a factor `(x/2)^{2/log x} ≈ 6.7` (module header). OPEN. -/
def YuttoMid2 : Prop :=
  ∀ x : ℝ, 1000000 ≤ x → x < 10000000000 →
    |HC.gYutto 2 x| ≤ (1634.34 + 817.168 * Real.log x) / x

/-- **Link [YuttoBig2] — `lem:yutto`, `v = 2`, large range** (`minarcs.tex` 2858-2877):
`|g₂(x)| ≤ 0.038128/(log x)² + 0.2046/√x` for `x ≥ 10¹⁰`. Helfgott's own lemma, stated
verbatim; its printed last step is false at `x = 10¹⁰` (needs `1.3165`, module header). OPEN. -/
def YuttoBig2 : Prop :=
  ∀ x : ℝ, 10000000000 ≤ x → |HC.gYutto 2 x| ≤ 0.038128 / Real.log x ^ 2 + 0.2046 / Real.sqrt x

/-- **Link [WeightEM] — `eq:etex`, odd version, `v = 2`** (`minarcs.tex` 3150-3172): the weight
of `g₂(m)` is `(1/4)log(1 + 1/m)` up to `(5m² + 2m + 1)/S²`. Helfgott prints the error with the
factor `c_{2,0} = 1/3`; only the factor `1` is needed here (measured worst ratio `0.217`). -/
def WeightEM : Prop :=
  ∀ m : ℕ, 1 ≤ m → ∀ S : ℝ, 10 * (m : ℝ) ≤ S →
    |wt m S - Real.log (1 + 1 / (m : ℝ)) / 4| ≤ (5 * (m : ℝ) ^ 2 + 2 * m + 1) / S ^ 2

/-! ## (1) Pointwise facts about `g₂` -/

theorem term_le (r1 r2 : ℕ) (h1 : 1 ≤ r1) (h2 : 1 ≤ r2) :
    |((ArithmeticFunction.moebius r1 : ℤ) : ℝ) * ((ArithmeticFunction.moebius r2 : ℤ) : ℝ) /
      ((ArithmeticFunction.sigma 1 r1 : ℝ) * (ArithmeticFunction.sigma 1 r2 : ℝ))| ≤ 1 := by
  have s1 : (1 : ℝ) ≤ (ArithmeticFunction.sigma 1 r1 : ℝ) := by
    exact_mod_cast ArithmeticFunction.sigma_pos 1 r1 (by omega)
  have s2 : (1 : ℝ) ≤ (ArithmeticFunction.sigma 1 r2 : ℝ) := by
    exact_mod_cast ArithmeticFunction.sigma_pos 1 r2 (by omega)
  have m1 : |((ArithmeticFunction.moebius r1 : ℤ) : ℝ)| ≤ 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  have m2 : |((ArithmeticFunction.moebius r2 : ℤ) : ℝ)| ≤ 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  have hp : (0 : ℝ) < (ArithmeticFunction.sigma 1 r1 : ℝ) * (ArithmeticFunction.sigma 1 r2 : ℝ) :=
    by positivity
  rw [abs_div, abs_mul, abs_of_pos hp, div_le_one hp]
  have h12 := mul_le_mul m1 m2 (abs_nonneg _) zero_le_one
  nlinarith

theorem abs_dsum_le (I : Finset ℕ) (F : ℕ → ℕ → ℝ) (hF : ∀ a ∈ I, ∀ b ∈ I, |F a b| ≤ 1) :
    |∑ a ∈ I, ∑ b ∈ I, F a b| ≤ (I.card : ℝ) ^ 2 := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have h : ∀ a ∈ I, |∑ b ∈ I, F a b| ≤ (I.card : ℝ) := by
    intro a ha
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have := Finset.sum_le_card_nsmul I (fun b => |F a b|) 1 (fun b hb => hF a ha b hb)
    simpa using this
  have := Finset.sum_le_card_nsmul I (fun a => |∑ b ∈ I, F a b|) (I.card : ℝ) h
  rw [nsmul_eq_mul] at this
  nlinarith

/-- Crude size bound `|g₂(x)| ≤ ⌊x⌋²` (each of the `⌊x⌋²` summands is at most `1`). -/
theorem gabs_le (x : ℝ) : |HC.gYutto 2 x| ≤ (⌊x⌋₊ : ℝ) ^ 2 := by
  unfold HC.gYutto
  refine (abs_dsum_le _ _ fun a ha b hb => ?_).trans (by simp)
  have ha1 := (Finset.mem_Icc.mp ha).1
  have hb1 := (Finset.mem_Icc.mp hb).1
  split_ifs
  · exact term_le a b ha1 hb1
  · simp

theorem g_zero : HC.gYutto 2 ((0 : ℕ) : ℝ) = 0 := by
  simp [HC.gYutto]

/-- `g₂(x) = ∑_{m ≤ 10⁴} g₂(m)𝟙[⌊x⌋ = m] + tl(x)`, for every real `x`. -/
theorem decomp_pt (x : ℝ) :
    HC.gYutto 2 x = (∑ m ∈ Finset.range 10001,
      HC.gYutto 2 (m : ℝ) * (if ⌊x⌋₊ = m then 1 else 0)) + tl x := by
  have hg := M2G.gY_floor x
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_range]
  unfold tl
  by_cases hk : ⌊x⌋₊ < 10001
  · have hx : ¬ (10001 : ℝ) ≤ x := by
      intro h
      have := Nat.le_floor (show ((10001 : ℕ) : ℝ) ≤ x by exact_mod_cast h)
      omega
    rw [if_pos hk, if_neg hx, hg]
    ring
  · have h1 : 10001 ≤ ⌊x⌋₊ := by omega
    have h0 : 0 ≤ x := by
      by_contra h
      rw [Nat.floor_of_nonpos (not_le.mp h).le] at h1
      omega
    have hx : (10001 : ℝ) ≤ x :=
      le_trans (by exact_mod_cast h1) (Nat.floor_le h0)
    rw [if_neg hk, if_pos hx]
    ring

/-! ## (2) Splitting one summand of `eq:grotto` -/

theorem meas_lin (S : ℝ) (s : ℕ) : Measurable fun u : ℝ => u * S / s :=
  (measurable_id.mul_const S).div_const _

theorem meas_g (S : ℝ) (s : ℕ) : Measurable fun u : ℝ => HC.gYutto 2 (u * S / s) := by
  have h : (fun u : ℝ => HC.gYutto 2 (u * S / s)) =
      (fun t : ℝ => (fun k : ℕ => HC.gYutto 2 (k : ℝ)) ⌊t⌋₊) ∘ (fun u : ℝ => u * S / s) :=
    funext fun u => M2G.gY_floor _
  rw [h]
  exact (M2G.meas_step (fun k : ℕ => HC.gYutto 2 (k : ℝ))).comp (meas_lin S s)

theorem meas_ind (m : ℕ) (S : ℝ) (s : ℕ) : Measurable fun u : ℝ => ind m S s u :=
  (M2G.meas_step (fun k : ℕ => if k = m then (1 : ℝ) else 0)).comp (meas_lin S s)

theorem meas_tl (S : ℝ) (s : ℕ) : Measurable fun u : ℝ => tl (u * S / s) :=
  Measurable.ite (measurableSet_le measurable_const (meas_lin S s)) (meas_g S s)
    measurable_const

theorem floor_le_S (S : ℝ) (hS : 0 ≤ S) (s : ℕ) (hs : 1 ≤ s) (u : ℝ) (hu : u ≤ 1) :
    ⌊u * S / s⌋₊ ≤ ⌊S⌋₊ := by
  apply Nat.floor_mono
  have hs0 : (1 : ℝ) ≤ s := by exact_mod_cast hs
  rw [div_le_iff₀ (by linarith)]
  nlinarith

theorem ii_g (S : ℝ) (hS : 0 ≤ S) (s : ℕ) (hs : 1 ≤ s) :
    IntervalIntegrable (fun u : ℝ => HC.gYutto 2 (u * S / s)) volume (1 / 2) 1 := by
  refine M2H.ii_of_bdd _ (meas_g S s) ((⌊S⌋₊ : ℝ) ^ 2) _ _ (by norm_num) fun u hu => ?_
  refine (gabs_le _).trans ?_
  have := floor_le_S S hS s hs u hu.2
  have h : (⌊u * S / s⌋₊ : ℝ) ≤ ⌊S⌋₊ := by exact_mod_cast this
  exact pow_le_pow_left₀ (Nat.cast_nonneg _) h 2

theorem ii_tl (S : ℝ) (hS : 0 ≤ S) (s : ℕ) (hs : 1 ≤ s) :
    IntervalIntegrable (fun u : ℝ => tl (u * S / s)) volume (1 / 2) 1 := by
  refine M2H.ii_of_bdd _ (meas_tl S s) ((⌊S⌋₊ : ℝ) ^ 2) _ _ (by norm_num) fun u hu => ?_
  unfold tl
  split_ifs
  · refine (gabs_le _).trans ?_
    have := floor_le_S S hS s hs u hu.2
    have h : (⌊u * S / s⌋₊ : ℝ) ≤ ⌊S⌋₊ := by exact_mod_cast this
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) h 2
  · simp only [abs_zero]
    positivity

theorem ii_ind (m : ℕ) (S : ℝ) (s : ℕ) :
    IntervalIntegrable (fun u : ℝ => ind m S s u) volume (1 / 2) 1 := by
  refine M2H.ii_of_bdd _ (meas_ind m S s) 1 _ _ (by norm_num) fun u _ => ?_
  unfold ind
  split_ifs <;> simp

theorem int_split (S : ℝ) (hS : 0 ≤ S) (s : ℕ) (hs : 1 ≤ s) :
    ∫ u in (1 / 2 : ℝ)..1, HC.gYutto 2 (u * S / s) =
      (∑ m ∈ Finset.range 10001, HC.gYutto 2 (m : ℝ) * ∫ u in (1 / 2 : ℝ)..1, ind m S s u) +
        ∫ u in (1 / 2 : ℝ)..1, tl (u * S / s) := by
  have e1 : ∫ u in (1 / 2 : ℝ)..1, (∑ m ∈ Finset.range 10001,
      HC.gYutto 2 (m : ℝ) * ind m S s u) =
      ∑ m ∈ Finset.range 10001, HC.gYutto 2 (m : ℝ) * ∫ u in (1 / 2 : ℝ)..1, ind m S s u := by
    rw [intervalIntegral.integral_finsetSum fun m _ => (ii_ind m S s).const_mul _]
    exact Finset.sum_congr rfl fun m _ => intervalIntegral.integral_const_mul _ _
  have e2 : ∫ u in (1 / 2 : ℝ)..1, (∑ m ∈ Finset.range 10001,
      HC.gYutto 2 (m : ℝ) * ind m S s u) =
      (∫ u in (1 / 2 : ℝ)..1, HC.gYutto 2 (u * S / s)) -
        ∫ u in (1 / 2 : ℝ)..1, tl (u * S / s) := by
    rw [← intervalIntegral.integral_sub (ii_g S hS s hs) (ii_tl S hS s hs)]
    refine intervalIntegral.integral_congr fun u _ => ?_
    have h := decomp_pt (u * S / s)
    simp only [ind]
    linarith
  linarith

/-- **`eq:grotto` = (the `m ≤ 10⁴` weights) + (the tail)**, exactly. -/
theorem corto_split (S : ℝ) (hS : 0 ≤ S) :
    HC.cortoLHS 2 S = (∑ m ∈ Finset.range 10001, HC.gYutto 2 (m : ℝ) * wt m S) +
      ∑ s ∈ (Finset.Icc 1 ⌊S⌋₊).filter (fun s => Nat.Coprime s 2),
        1 / (s : ℝ) * ∫ u in (1 / 2 : ℝ)..1, tl (u * S / s) := by
  unfold HC.cortoLHS wt
  have hs1 : ∀ s ∈ (Finset.Icc 1 ⌊S⌋₊).filter (fun s => Nat.Coprime s 2), 1 ≤ s :=
    fun s hs => (Finset.mem_Icc.mp (Finset.mem_filter.mp hs).1).1
  rw [Finset.sum_congr rfl fun s hs => by rw [int_split S hS s (hs1 s hs), mul_add],
    Finset.sum_add_distrib]
  refine congrArg (fun z => z + _) ?_
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun s _ => by ring

/-! ## (3) The main term: `m ≤ C₀ = 10⁴` -/

theorem range_eq : Finset.range 10001 = insert 0 (Finset.Icc 1 10000) := by
  ext m
  simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
  omega

/-- **`∑_{m ≤ 10⁴} g₂(m)·wt(m) ≤ 0.360577 + 47734020.6/S²`** for `S ≥ 10⁵` (`WeightEM` and the
cited `C₀ = 10⁴` sums). -/
theorem main_le (em : WeightEM) (c0 : HC.CortoC0Cited) (S : ℝ) (hS : 100000 ≤ S) :
    ∑ m ∈ Finset.range 10001, HC.gYutto 2 (m : ℝ) * wt m S ≤
      0.360577 + 47734020.6 / S ^ 2 := by
  have hS0 : 0 < S := by linarith
  rw [range_eq, Finset.sum_insert (by simp), g_zero, zero_mul, zero_add]
  have hmain : HC.cortoMain 2 = 1 / 4 * ∑ m ∈ Finset.Icc (1 : ℕ) 10000,
      HC.gYutto 2 (m : ℝ) * Real.log (1 + 1 / (m : ℝ)) := by
    unfold HC.cortoMain
    rw [Nat.totient_two]
    norm_num
  have herr : HC.cortoErr 2 (1 / 3) = 1 / 3 * ∑ m ∈ Finset.Icc (1 : ℕ) 10000,
      |HC.gYutto 2 (m : ℝ)| * (5 * (m : ℝ) ^ 2 + 2 * (m : ℝ) + 1) := rfl
  have key : ∑ m ∈ Finset.Icc (1 : ℕ) 10000, HC.gYutto 2 (m : ℝ) * wt m S ≤
      1 / 4 * (∑ m ∈ Finset.Icc (1 : ℕ) 10000, HC.gYutto 2 (m : ℝ) * Real.log (1 + 1 / (m : ℝ))) +
        (∑ m ∈ Finset.Icc (1 : ℕ) 10000,
          |HC.gYutto 2 (m : ℝ)| * (5 * (m : ℝ) ^ 2 + 2 * (m : ℝ) + 1)) / S ^ 2 := by
    rw [Finset.sum_div, Finset.mul_sum, ← sub_le_iff_le_add', ← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun m hm => ?_
    have hm1 := (Finset.mem_Icc.mp hm).1
    have hm2 : (m : ℝ) ≤ 10000 := by exact_mod_cast (Finset.mem_Icc.mp hm).2
    have h := em m hm1 S (by linarith)
    calc HC.gYutto 2 (m : ℝ) * wt m S - 1 / 4 * (HC.gYutto 2 (m : ℝ) *
          Real.log (1 + 1 / (m : ℝ)))
        = HC.gYutto 2 (m : ℝ) * (wt m S - Real.log (1 + 1 / (m : ℝ)) / 4) := by ring
      _ ≤ |HC.gYutto 2 (m : ℝ) * (wt m S - Real.log (1 + 1 / (m : ℝ)) / 4)| := le_abs_self _
      _ = |HC.gYutto 2 (m : ℝ)| * |wt m S - Real.log (1 + 1 / (m : ℝ)) / 4| := abs_mul _ _
      _ ≤ |HC.gYutto 2 (m : ℝ)| * ((5 * (m : ℝ) ^ 2 + 2 * m + 1) / S ^ 2) :=
          mul_le_mul_of_nonneg_left h (abs_nonneg _)
      _ = |HC.gYutto 2 (m : ℝ)| * (5 * (m : ℝ) ^ 2 + 2 * (m : ℝ) + 1) / S ^ 2 := by ring
  have hc1 := c0.2.1.2
  have hc2 := c0.2.2.2
  rw [herr] at hc2
  rw [hmain] at hc1
  have hS2 : 0 < S ^ 2 := by positivity
  have hd : (∑ m ∈ Finset.Icc (1 : ℕ) 10000,
      |HC.gYutto 2 (m : ℝ)| * (5 * (m : ℝ) ^ 2 + 2 * (m : ℝ) + 1)) / S ^ 2 ≤
        47734020.6 / S ^ 2 :=
    div_le_div_of_nonneg_right (by linarith) hS2.le
  linarith

/-! ## (4) The tail, one `s` at a time -/

/-- The `10001 ≤ uS/s ≤ 10⁶` coefficient (`HC.YuttoSmallCited`: `|g₂(x)| ≤ 2.1/x`). -/
noncomputable def a1 (S : ℝ) (s : ℕ) : ℝ := if (s : ℝ) ≤ S / 10001 then 2.1 else 0

/-- The `10⁶ < uS/s < 10¹⁰` coefficient (`YuttoMid2`, with `log(uS/s) ≤ log(S/s)`). -/
noncomputable def a2 (S : ℝ) (s : ℕ) : ℝ :=
  if (s : ℝ) ≤ S / 1000000 then 1634.34 + 817.168 * Real.log (S / s) else 0

/-- The `uS/s ≥ 10¹⁰` majorant (`YuttoBig2`, with `uS/s ≥ S/2s`). -/
noncomputable def bC (S : ℝ) (s : ℕ) : ℝ :=
  if (s : ℝ) ≤ S / 10000000000 then
    0.038128 / Real.log (S / (2 * s)) ^ 2 + 0.2046 / Real.sqrt (S / (2 * s))
  else 0

theorem a1_nonneg (S : ℝ) (s : ℕ) : 0 ≤ a1 S s := by
  unfold a1
  split_ifs <;> norm_num

theorem a2_nonneg (S : ℝ) (s : ℕ) (hs : 1 ≤ s) : 0 ≤ a2 S s := by
  unfold a2
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  split_ifs with h
  · have h1 : 1 ≤ S / s := by
      rw [le_div_iff₀ hs0]
      have := (le_div_iff₀ (by norm_num : (0 : ℝ) < 1000000)).mp h
      linarith
    have := Real.log_nonneg h1
    nlinarith
  · exact le_rfl

theorem bC_nonneg (S : ℝ) (s : ℕ) : 0 ≤ bC S s := by
  unfold bC
  split_ifs
  · positivity
  · exact le_rfl

/-- **Pointwise tail majorant** on `u ∈ [1/2, 1]`. -/
theorem tl_pt (ys : HC.YuttoSmallCited) (ym : YuttoMid2) (yb : YuttoBig2) (S : ℝ) (hS : 0 < S)
    (s : ℕ) (hs : 1 ≤ s) (u : ℝ) (hu1 : 1 / 2 ≤ u) (hu2 : u ≤ 1) :
    |tl (u * S / s)| ≤ (a1 S s + a2 S s) * ((s : ℝ) / S / u) + bC S s := by
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  have hu0 : 0 < u := by linarith
  have hx0 : 0 < u * S / s := by positivity
  have hxr : 1 / (u * S / s) = (s : ℝ) / S / u := by field_simp
  have hxS : u * S / s ≤ S / s := by
    rw [div_le_div_iff_of_pos_right hs0]
    nlinarith
  have hxS2 : S / (2 * s) ≤ u * S / s := by
    rw [div_le_div_iff₀ (by positivity) hs0]
    have : 0 ≤ (2 * u - 1) * (S * s) := mul_nonneg (by linarith) (by positivity)
    nlinarith
  have ha := add_nonneg (a1_nonneg S s) (a2_nonneg S s hs)
  have hb := bC_nonneg S s
  have hr0 : 0 ≤ (s : ℝ) / S / u := by positivity
  have har := mul_nonneg ha hr0
  have hcond : ∀ c : ℝ, 0 < c → c ≤ u * S / s → (s : ℝ) ≤ S / c := by
    intro c hc h
    have h' := le_trans h hxS
    rw [le_div_iff₀ hs0] at h'
    rw [le_div_iff₀ hc]
    linarith
  unfold tl
  split_ifs with h1
  swap
  · rw [abs_zero]
    linarith
  rcases le_or_gt (u * S / s) 1000000 with h2 | h2
  · have hg := (ys (u * S / s) (by linarith) h2).2
    have hc : a1 S s = 2.1 := by
      unfold a1
      rw [if_pos (hcond 10001 (by norm_num) h1)]
    have h2a := a2_nonneg S s hs
    calc |HC.gYutto 2 (u * S / s)| ≤ 2.1 / (u * S / s) := hg
      _ = 2.1 * (1 / (u * S / s)) := by ring
      _ = 2.1 * ((s : ℝ) / S / u) := by rw [hxr]
      _ ≤ (a1 S s + a2 S s) * ((s : ℝ) / S / u) :=
          mul_le_mul_of_nonneg_right (by linarith) hr0
      _ ≤ _ := le_add_of_nonneg_right hb
  rcases lt_or_ge (u * S / s) 10000000000 with h3 | h3
  · have hg := ym (u * S / s) h2.le h3
    have hc : a2 S s = 1634.34 + 817.168 * Real.log (S / s) := by
      unfold a2
      rw [if_pos (hcond 1000000 (by norm_num) h2.le)]
    have hlog : Real.log (u * S / s) ≤ Real.log (S / s) := Real.log_le_log hx0 hxS
    have h1a := a1_nonneg S s
    calc |HC.gYutto 2 (u * S / s)| ≤ (1634.34 + 817.168 * Real.log (u * S / s)) / (u * S / s) :=
          hg
      _ = (1634.34 + 817.168 * Real.log (u * S / s)) * (1 / (u * S / s)) := by ring
      _ = (1634.34 + 817.168 * Real.log (u * S / s)) * ((s : ℝ) / S / u) := by rw [hxr]
      _ ≤ (a1 S s + a2 S s) * ((s : ℝ) / S / u) :=
          mul_le_mul_of_nonneg_right (by rw [hc]; linarith) hr0
      _ ≤ _ := le_add_of_nonneg_right hb
  · have hg := yb (u * S / s) h3
    have hc := hcond 10000000000 (by norm_num) h3
    have hS2 : 1 < S / (2 * s) := by
      rw [lt_div_iff₀ (by positivity)]
      rw [le_div_iff₀ (by norm_num)] at hc
      linarith
    have hL : 0 < Real.log (S / (2 * s)) := Real.log_pos hS2
    have hlog : Real.log (S / (2 * s)) ≤ Real.log (u * S / s) :=
      Real.log_le_log (by linarith) hxS2
    have e1 : 0.038128 / Real.log (u * S / s) ^ 2 ≤ 0.038128 / Real.log (S / (2 * s)) ^ 2 :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) (pow_le_pow_left₀ hL.le hlog 2)
    have e2 : 0.2046 / Real.sqrt (u * S / s) ≤ 0.2046 / Real.sqrt (S / (2 * s)) :=
      div_le_div_of_nonneg_left (by norm_num) (Real.sqrt_pos.2 (by linarith))
        (Real.sqrt_le_sqrt hxS2)
    have hbC : bC S s = 0.038128 / Real.log (S / (2 * s)) ^ 2 +
        0.2046 / Real.sqrt (S / (2 * s)) := by
      unfold bC
      rw [if_pos hc]
    linarith

/-- **One summand of the tail**: `(1/s)∫_{1/2}^{1} tl(uS/s) du ≤ (log 2/S)(a₁ + a₂) + bC/(2s)`. -/
theorem tail_s (ys : HC.YuttoSmallCited) (ym : YuttoMid2) (yb : YuttoBig2) (S : ℝ) (hS : 0 < S)
    (s : ℕ) (hs : 1 ≤ s) :
    1 / (s : ℝ) * ∫ u in (1 / 2 : ℝ)..1, tl (u * S / s) ≤
      Real.log 2 / S * (a1 S s + a2 S s) + 1 / (2 * s) * bC S s := by
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  have hii1 : IntervalIntegrable (fun u : ℝ => (a1 S s + a2 S s) * ((s : ℝ) / S / u))
      volume (1 / 2) 1 := by
    refine ContinuousOn.intervalIntegrable ?_
    refine continuousOn_const.mul (continuousOn_const.div continuousOn_id ?_)
    intro u hu
    rw [uIcc_of_le (by norm_num)] at hu
    exact ne_of_gt (by linarith [hu.1])
  have hinv : ∫ u in (1 / 2 : ℝ)..1, (s : ℝ) / S / u = (s : ℝ) / S * Real.log 2 := by
    have h : ∀ u : ℝ, (s : ℝ) / S / u = (s : ℝ) / S * u⁻¹ := fun u => by ring
    simp_rw [h]
    rw [intervalIntegral.integral_const_mul, integral_inv_of_pos (by norm_num) (by norm_num)]
    norm_num
  have hint : ∫ u in (1 / 2 : ℝ)..1, ((a1 S s + a2 S s) * ((s : ℝ) / S / u) + bC S s) =
      (a1 S s + a2 S s) * ((s : ℝ) / S * Real.log 2) + bC S s / 2 := by
    rw [intervalIntegral.integral_add hii1 intervalIntegrable_const,
      intervalIntegral.integral_const_mul, hinv, intervalIntegral.integral_const, smul_eq_mul]
    ring
  have h1 : |∫ u in (1 / 2 : ℝ)..1, tl (u * S / s)| ≤
      ∫ u in (1 / 2 : ℝ)..1, |tl (u * S / s)| :=
    intervalIntegral.abs_integral_le_integral_abs (by norm_num)
  have h2 : ∫ u in (1 / 2 : ℝ)..1, |tl (u * S / s)| ≤
      ∫ u in (1 / 2 : ℝ)..1, ((a1 S s + a2 S s) * ((s : ℝ) / S / u) + bC S s) :=
    intervalIntegral.integral_mono_on (by norm_num) (ii_tl S hS.le s hs).abs
      (hii1.add intervalIntegrable_const) fun u hu => tl_pt ys ym yb S hS s hs u hu.1 hu.2
  have hpos : 0 ≤ 1 / (s : ℝ) := by positivity
  calc 1 / (s : ℝ) * ∫ u in (1 / 2 : ℝ)..1, tl (u * S / s)
      ≤ 1 / (s : ℝ) * |∫ u in (1 / 2 : ℝ)..1, tl (u * S / s)| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) hpos
    _ ≤ 1 / (s : ℝ) * ((a1 S s + a2 S s) * ((s : ℝ) / S * Real.log 2) + bC S s / 2) :=
        mul_le_mul_of_nonneg_left (by rw [← hint]; linarith) hpos
    _ = Real.log 2 / S * (a1 S s + a2 S s) + 1 / (2 * s) * bC S s := by
        field_simp

/-! ## (5) Sums over odd `s` -/

theorem odd_mem (N : ℕ) (X : ℝ) (s : ℕ)
    (hs : s ∈ (Finset.Icc 1 N).filter (fun s => Nat.Coprime s 2)) (hsX : (s : ℝ) ≤ X) :
    s ∈ (Finset.range ⌊(X + 1) / 2⌋₊).image (fun k => 2 * k + 1) := by
  have hc := (Finset.mem_filter.mp hs).2
  have hnd : ¬ 2 ∣ s := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp hc.symm
  rw [Finset.mem_image]
  refine ⟨s / 2, Finset.mem_range.mpr ?_, by omega⟩
  refine Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_floor ?_)
  have h2 : 2 * (s / 2 + 1) = s + 1 := by omega
  have hr : (2 : ℝ) * ((s / 2 + 1 : ℕ) : ℝ) = (s : ℝ) + 1 := by exact_mod_cast h2
  linarith

theorem range_le (X : ℝ) (hX : 0 ≤ X) (k : ℕ) (hk : k ∈ Finset.range ⌊(X + 1) / 2⌋₊) :
    2 * (k : ℝ) + 1 ≤ X := by
  have h0 := Finset.mem_range.mp hk
  have h1 : ((k + 1 : ℕ) : ℝ) ≤ ⌊(X + 1) / 2⌋₊ := by exact_mod_cast h0
  have h2 := Nat.floor_le (show 0 ≤ (X + 1) / 2 by linarith)
  push_cast at h1
  linarith

/-- A sum over odd `s ≤ N` of a function vanishing beyond `X` is at most the sum over the first
`⌊(X+1)/2⌋` odd numbers. -/
theorem odd_sum_le (N : ℕ) (X : ℝ) (f : ℕ → ℝ) (hz : ∀ s : ℕ, X < s → f s = 0)
    (hf : ∀ k ∈ Finset.range ⌊(X + 1) / 2⌋₊, 0 ≤ f (2 * k + 1)) :
    ∑ s ∈ (Finset.Icc 1 N).filter (fun s => Nat.Coprime s 2), f s ≤
      ∑ k ∈ Finset.range ⌊(X + 1) / 2⌋₊, f (2 * k + 1) := by
  rw [← Finset.sum_filter_of_ne (p := fun s : ℕ => (s : ℝ) ≤ X)
    (fun s _ h => by
      by_contra h'
      exact h (hz s (not_le.mp h')))]
  rw [← Finset.sum_image (s := Finset.range ⌊(X + 1) / 2⌋₊) (g := fun k => 2 * k + 1) (f := f)
    (fun a _ b _ h => by simp only at h; omega)]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro s hs
    rw [Finset.mem_filter] at hs
    exact odd_mem N X s hs.1 hs.2
  · intro t ht _
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp ht
    exact hf k hk

/-- `∑_{k < K} 1/√(2k+1) ≤ √(2K)` (telescoping `1/√(2k+1) ≤ √(2k+2) − √(2k)`). -/
theorem inv_sqrt_sum (K : ℕ) :
    ∑ k ∈ Finset.range K, 1 / Real.sqrt (2 * (k : ℝ) + 1) ≤ Real.sqrt (2 * (K : ℝ)) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ]
    have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    set a := Real.sqrt (2 * (K : ℝ)) with ha_def
    set c := Real.sqrt (2 * (K : ℝ) + 1) with hc_def
    have hb_def : Real.sqrt (2 * ((K + 1 : ℕ) : ℝ)) = Real.sqrt (2 * (K : ℝ) + 2) := by
      push_cast
      ring_nf
    rw [hb_def]
    set b := Real.sqrt (2 * (K : ℝ) + 2) with hb
    have ha0 : 0 ≤ a := Real.sqrt_nonneg _
    have hb0 : 0 ≤ b := Real.sqrt_nonneg _
    have hc0 : 0 < c := Real.sqrt_pos.2 (by linarith)
    have ha2 : a ^ 2 = 2 * (K : ℝ) := Real.sq_sqrt (by linarith)
    have hb2 : b ^ 2 = 2 * (K : ℝ) + 2 := Real.sq_sqrt (by linarith)
    have hc2 : c ^ 2 = 2 * (K : ℝ) + 1 := Real.sq_sqrt (by linarith)
    have hab : a ≤ b := Real.sqrt_le_sqrt (by linarith)
    have hsum : a + b ≤ 2 * c := by nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - 2 * c)]
    have hprod : 1 ≤ c * (b - a) := by
      have h := mul_le_mul_of_nonneg_left hsum (sub_nonneg.2 hab)
      nlinarith
    have hinv : 1 / c ≤ b - a := by
      rw [div_le_iff₀ hc0]
      linarith
    linarith

/-! ## (6) The three tail sums -/

theorem log_1e6 : Real.log 1000000 ≤ 13.98 := by
  have h : (1000000 : ℝ) = 2 ^ 18 * (5 / 4) ^ 6 := by norm_num
  rw [h, Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  have h1 := Real.log_two_lt_d9
  have h2 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 5 / 4 by norm_num)
  push_cast
  linarith

/-- **The `10⁶ ≤ S/s` sum**: `∑_{k<K} a₂(2k+1) ≤ K(1634.34 + 817.168·11.98) + 1634.336√(S/10⁶)√(2K)`
(`log(S/s) = log 10⁶ + log(T/s)`, `log z ≤ 2(√z − 1)`, `inv_sqrt_sum`). -/
theorem sum2_le (S : ℝ) (hS : 0 < S) (K : ℕ)
    (hK : ∀ k ∈ Finset.range K, 2 * (k : ℝ) + 1 ≤ S / 1000000) :
    ∑ k ∈ Finset.range K, a2 S (2 * k + 1) ≤
      K * (1634.34 + 817.168 * 11.98) +
        2 * 817.168 * Real.sqrt (S / 1000000) * Real.sqrt (2 * (K : ℝ)) := by
  have hterm : ∀ k ∈ Finset.range K, a2 S (2 * k + 1) ≤ (1634.34 + 817.168 * 11.98) +
      2 * 817.168 * Real.sqrt (S / 1000000) * (1 / Real.sqrt (2 * (k : ℝ) + 1)) := by
    intro k hk
    have hc := hK k hk
    have hs0 : (0 : ℝ) < 2 * k + 1 := by positivity
    unfold a2
    push_cast
    rw [if_pos hc]
    have e1 : Real.log (S / (2 * k + 1)) =
        Real.log 1000000 + Real.log (S / 1000000 / (2 * k + 1)) := by
      rw [← Real.log_mul (by norm_num) (by positivity)]
      congr 1
      field_simp
    have e2 : Real.log (S / 1000000 / (2 * k + 1)) ≤
        2 * (Real.sqrt (S / 1000000 / (2 * k + 1)) - 1) := by
      have := Real.log_le_sub_one_of_pos
        (Real.sqrt_pos.2 (by positivity : (0 : ℝ) < S / 1000000 / (2 * k + 1)))
      rw [Real.log_sqrt (by positivity)] at this
      linarith
    have e3 : Real.sqrt (S / 1000000 / (2 * k + 1)) =
        Real.sqrt (S / 1000000) * (1 / Real.sqrt (2 * k + 1)) := by
      rw [Real.sqrt_div' _ hs0.le]
      ring
    have := log_1e6
    rw [e1]
    rw [e3] at e2
    linarith
  calc ∑ k ∈ Finset.range K, a2 S (2 * k + 1)
      ≤ ∑ k ∈ Finset.range K, ((1634.34 + 817.168 * 11.98) +
          2 * 817.168 * Real.sqrt (S / 1000000) * (1 / Real.sqrt (2 * (k : ℝ) + 1))) :=
        Finset.sum_le_sum hterm
    _ = K * (1634.34 + 817.168 * 11.98) + 2 * 817.168 * Real.sqrt (S / 1000000) *
          ∑ k ∈ Finset.range K, 1 / Real.sqrt (2 * (k : ℝ) + 1) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
          ← Finset.mul_sum]
    _ ≤ _ := by
        have h := mul_le_mul_of_nonneg_left (inv_sqrt_sum K)
          (by positivity : (0 : ℝ) ≤ 2 * 817.168 * Real.sqrt (S / 1000000))
        linarith

/-- `L(k) = log(S/(2(2k+1)))`. -/
noncomputable def lg (S : ℝ) (k : ℕ) : ℝ := Real.log (S / (2 * (2 * (k : ℝ) + 1)))

theorem exp22 : Real.exp 22 ≤ 5000000000 := by
  have h := Real.exp_one_lt_d9
  have h22 : Real.exp 22 = Real.exp 1 ^ 22 := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [h22]
  calc Real.exp 1 ^ 22 ≤ (2.7182818286 : ℝ) ^ 22 :=
        pow_le_pow_left₀ (Real.exp_pos 1).le h.le 22
    _ ≤ 5000000000 := by norm_num

theorem lg_ge (S : ℝ) (k : ℕ) (hk : 2 * (k : ℝ) + 1 ≤ S / 10000000000) : 22 ≤ lg S k := by
  unfold lg
  have hs1 : (1 : ℝ) ≤ 2 * k + 1 := by
    have := Nat.cast_nonneg (α := ℝ) k
    linarith
  rw [le_div_iff₀ (by norm_num)] at hk
  have h5 : 5000000000 ≤ S / (2 * (2 * (k : ℝ) + 1)) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  rw [Real.le_log_iff_exp_le (by linarith)]
  linarith [exp22]

/-- One telescoping step: `1/(sL(s)²) ≤ 0.54(1/L(s) − 1/L(s−2))`, `s = 2n+3`. -/
theorem tel_step (S : ℝ) (n : ℕ) (hn : 2 * ((n + 1 : ℕ) : ℝ) + 1 ≤ S / 10000000000) :
    1 / (2 * ((n + 1 : ℕ) : ℝ) + 1) * (1 / lg S (n + 1) ^ 2) ≤
      0.54 * (1 / lg S (n + 1) - 1 / lg S n) := by
  have hL := lg_ge S (n + 1) hn
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hS : 0 < S := by
    have : (0 : ℝ) < S / 10000000000 := by push_cast at hn; linarith
    have h' := (div_pos_iff.mp this)
    rcases h' with h' | h'
    · exact h'.1
    · norm_num at h'
  set L := lg S (n + 1) with hLdef
  set δ := Real.log ((2 * (n : ℝ) + 3) / (2 * n + 1)) with hδdef
  have hlgn : lg S n = L + δ := by
    rw [hLdef, hδdef]
    unfold lg
    rw [← Real.log_mul (by positivity) (by positivity)]
    congr 1
    push_cast
    field_simp
    ring
  have hδl : 2 ≤ δ * (2 * (n : ℝ) + 3) := by
    have h := Real.one_sub_inv_le_log_of_pos
      (show (0 : ℝ) < (2 * (n : ℝ) + 3) / (2 * n + 1) by positivity)
    rw [inv_div] at h
    have e : 1 - (2 * (n : ℝ) + 1) / (2 * n + 3) = 2 / (2 * n + 3) := by
      field_simp
      ring
    rw [e, div_le_iff₀ (by positivity)] at h
    linarith
  have hδu : δ ≤ 0.08 * L := by
    have h4 : (2 * (n : ℝ) + 3) / (2 * n + 1) ≤ 4 := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    have hl4 : δ ≤ Real.log 4 := Real.log_le_log (by positivity) h4
    have e4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    have := Real.log_two_lt_d9
    linarith
  have hδ0 : 0 ≤ δ := by nlinarith
  have hL0 : 0 < L := by linarith
  rw [hlgn]
  have e : 1 / L - 1 / (L + δ) = δ / (L * (L + δ)) := by
    field_simp
    ring
  rw [e]
  push_cast
  rw [show 1 / (2 * ((n : ℝ) + 1) + 1) * (1 / L ^ 2) = 1 / ((2 * (n : ℝ) + 3) * L ^ 2) by
    rw [div_mul_div_comm, one_mul]
    congr 1
    ring]
  rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg (sub_nonneg.2 hδl) (sq_nonneg L), mul_nonneg (sub_nonneg.2 hδu) hL0.le]

/-- **The telescoped `1/(s log²(S/2s))` sum** over odd `s ≤ 2n+1 ≤ S/10¹⁰`. -/
theorem tel (S : ℝ) (n : ℕ) (hn : 2 * (n : ℝ) + 1 ≤ S / 10000000000) :
    ∑ k ∈ Finset.range (n + 1), 1 / (2 * (k : ℝ) + 1) * (1 / lg S k ^ 2) ≤
      1 / 484 + 0.54 * (1 / lg S n - 1 / lg S 0) := by
  induction n with
  | zero =>
    rw [Finset.sum_range_one, sub_self, mul_zero, add_zero]
    have hL := lg_ge S 0 hn
    have hL0 : 0 < lg S 0 := by linarith
    push_cast
    rw [mul_zero, zero_add, div_one, one_mul, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hn' : 2 * (n : ℝ) + 1 ≤ S / 10000000000 := by
      push_cast at hn
      linarith
    have h1 := ih hn'
    have h2 := tel_step S n hn
    linarith

theorem sq_term (S s : ℝ) (hS : 0 < S) (hs : 0 < s) :
    1 / (2 * s) * (0.2046 / Real.sqrt (S / (2 * s))) =
      0.2046 * (1 / Real.sqrt (2 * S) * (1 / Real.sqrt s)) := by
  rw [Real.sqrt_div' S (by positivity : (0 : ℝ) ≤ 2 * s),
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) S, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) s]
  have hp : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hr : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs.le
  have hp0 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hq0 : 0 < Real.sqrt S := Real.sqrt_pos.2 hS
  have hr0 : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  have key : Real.sqrt 2 ^ 2 * Real.sqrt s ^ 2 = 2 * s := by rw [hp, hr]
  field_simp
  linear_combination key

/-- **The `S/s ≥ 10¹⁰` sum**: `≤ 0.019064(1/484 + 0.54/22) + 0.2046/10⁵`. -/
theorem sum3_le (S : ℝ) (hS : 0 < S) (K : ℕ)
    (hK : ∀ k ∈ Finset.range K, 2 * (k : ℝ) + 1 ≤ S / 10000000000)
    (hK2 : 2 * (K : ℝ) ≤ S / 10000000000 + 1) :
    ∑ k ∈ Finset.range K, 1 / (2 * ((2 * k + 1 : ℕ) : ℝ)) * bC S (2 * k + 1) ≤
      0.019064 * (1 / 484 + 0.54 / 22) + 0.2046 / 100000 := by
  rcases K with _ | n
  · simp only [Finset.range_zero, Finset.sum_empty]
    norm_num
  have hX : 1 ≤ S / 10000000000 := by
    have := hK 0 (by simp)
    push_cast at this
    linarith
  have hterm : ∀ k ∈ Finset.range (n + 1), 1 / (2 * ((2 * k + 1 : ℕ) : ℝ)) * bC S (2 * k + 1) =
      0.019064 * (1 / (2 * (k : ℝ) + 1) * (1 / lg S k ^ 2)) +
        0.2046 * (1 / Real.sqrt (2 * S) * (1 / Real.sqrt (2 * (k : ℝ) + 1))) := by
    intro k hk
    have hc := hK k hk
    unfold bC
    push_cast
    rw [if_pos hc, mul_add, sq_term S _ hS (by positivity)]
    unfold lg
    field_simp
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum]
  have h1 := tel S n (hK n (by simp))
  have hLn := lg_ge S n (hK n (by simp))
  have hL0 := lg_ge S 0 (hK 0 (by simp))
  have h1n : 1 / lg S n ≤ 1 / 22 := one_div_le_one_div_of_le (by norm_num) hLn
  have h10 : 0 ≤ 1 / lg S 0 := by
    have : 0 < lg S 0 := by linarith
    positivity
  have h2 := inv_sqrt_sum (n + 1)
  have hq : Real.sqrt (2 * ((n + 1 : ℕ) : ℝ)) ≤ Real.sqrt (2 * S) / 100000 := by
    have e : Real.sqrt (2 * S) / 100000 = Real.sqrt (2 * S / 10000000000) := by
      rw [Real.sqrt_div' _ (by norm_num)]
      congr 1
      rw [show (10000000000 : ℝ) = 100000 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [e]
    apply Real.sqrt_le_sqrt
    push_cast at hK2 ⊢
    have : S / 10000000000 + 1 ≤ 2 * S / 10000000000 := by
      rw [mul_div_assoc]
      linarith
    linarith
  have hS2 : 0 < Real.sqrt (2 * S) := Real.sqrt_pos.2 (by linarith)
  have h3 : 1 / Real.sqrt (2 * S) * ∑ k ∈ Finset.range (n + 1),
      1 / Real.sqrt (2 * (k : ℝ) + 1) ≤ 1 / 100000 := by
    calc 1 / Real.sqrt (2 * S) * ∑ k ∈ Finset.range (n + 1), 1 / Real.sqrt (2 * (k : ℝ) + 1)
        ≤ 1 / Real.sqrt (2 * S) * (Real.sqrt (2 * S) / 100000) :=
          mul_le_mul_of_nonneg_left (h2.trans hq) (by positivity)
      _ = 1 / 100000 := by field_simp
  nlinarith

/-! ## (7) `M2H.CortoLarge` from its links -/

/-- **`M2H.CortoLarge` from `lem:yutto`'s two large ranges, `WeightEM`, and the two cited
computations, PROVED.** The bound reached is `0.37083` (worst at `S = 10⁶`) against the
required `0.37273`. -/
theorem cortoLarge_of_links (ym : YuttoMid2) (yb : YuttoBig2) (em : WeightEM)
    (ys : HC.YuttoSmallCited) (c0 : HC.CortoC0Cited) : M2H.CortoLarge := by
  intro S hS
  have hS0 : 0 < S := by linarith
  rw [corto_split S hS0.le]
  have hA := main_le em c0 S hS
  set F := (Finset.Icc 1 ⌊S⌋₊).filter (fun s => Nat.Coprime s 2) with hF
  have hs1 : ∀ s ∈ F, 1 ≤ s := fun s hs => (Finset.mem_Icc.mp (Finset.mem_filter.mp hs).1).1
  have hB : ∑ s ∈ F, 1 / (s : ℝ) * ∫ u in (1 / 2 : ℝ)..1, tl (u * S / s) ≤
      Real.log 2 / S * ((∑ s ∈ F, a1 S s) + ∑ s ∈ F, a2 S s) +
        ∑ s ∈ F, 1 / (2 * (s : ℝ)) * bC S s := by
    refine (Finset.sum_le_sum fun s hs => tail_s ys ym yb S hS0 s (hs1 s hs)).trans
      (le_of_eq ?_)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_add_distrib]
  set K1 := ⌊(S / 10001 + 1) / 2⌋₊ with hK1def
  set K2 := ⌊(S / 1000000 + 1) / 2⌋₊ with hK2def
  set K3 := ⌊(S / 10000000000 + 1) / 2⌋₊ with hK3def
  have h1 : ∑ s ∈ F, a1 S s ≤ K1 * 2.1 := by
    refine (odd_sum_le ⌊S⌋₊ (S / 10001) (a1 S) (fun s hs => ?_)
      (fun k _ => a1_nonneg S _)).trans ?_
    · unfold a1
      rw [if_neg (not_le.mpr hs)]
    · have := Finset.sum_le_card_nsmul (Finset.range K1) (fun k => a1 S (2 * k + 1)) 2.1
        (fun k _ => by
          unfold a1
          split_ifs <;> norm_num)
      rw [Finset.card_range, nsmul_eq_mul] at this
      exact this
  have h2 : ∑ s ∈ F, a2 S s ≤ K2 * (1634.34 + 817.168 * 11.98) +
      2 * 817.168 * Real.sqrt (S / 1000000) * Real.sqrt (2 * (K2 : ℝ)) := by
    refine (odd_sum_le ⌊S⌋₊ (S / 1000000) (a2 S) (fun s hs => ?_)
      (fun k _ => a2_nonneg S _ (by omega))).trans
      (sum2_le S hS0 K2 fun k hk => range_le _ (by positivity) k hk)
    unfold a2
    rw [if_neg (not_le.mpr hs)]
  have h3 : ∑ s ∈ F, 1 / (2 * (s : ℝ)) * bC S s ≤
      0.019064 * (1 / 484 + 0.54 / 22) + 0.2046 / 100000 := by
    refine (odd_sum_le ⌊S⌋₊ (S / 10000000000) (fun s => 1 / (2 * (s : ℝ)) * bC S s)
      (fun s hs => ?_) (fun k _ => mul_nonneg (by positivity) (bC_nonneg S _))).trans
      (sum3_le S hS0 K3 (fun k hk => range_le _ (by positivity) k hk) ?_)
    · unfold bC
      rw [if_neg (not_le.mpr hs), mul_zero]
    · have := Nat.floor_le (show 0 ≤ (S / 10000000000 + 1) / 2 by positivity)
      linarith
  have hK1 : (K1 : ℝ) ≤ (S / 10001 + 1) / 2 := Nat.floor_le (by positivity)
  have hX0 : 0 ≤ (∑ s ∈ F, a1 S s) + ∑ s ∈ F, a2 S s :=
    add_nonneg (Finset.sum_nonneg fun s _ => a1_nonneg S s)
      (Finset.sum_nonneg fun s hs => a2_nonneg S s (hs1 s hs))
  have hl2 := Real.log_two_lt_d9
  have hl2' : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogX : ∀ M : ℝ, (∑ s ∈ F, a1 S s) + ∑ s ∈ F, a2 S s ≤ M * S →
      Real.log 2 / S * ((∑ s ∈ F, a1 S s) + ∑ s ∈ F, a2 S s) ≤ 0.6931471808 * M := by
    intro M hM
    have hq : ((∑ s ∈ F, a1 S s) + ∑ s ∈ F, a2 S s) / S ≤ M := by
      rw [div_le_iff₀ hS0]
      exact hM
    have hq0 : 0 ≤ ((∑ s ∈ F, a1 S s) + ∑ s ∈ F, a2 S s) / S := div_nonneg hX0 hS0.le
    rw [div_mul_eq_mul_div, mul_div_assoc]
    exact mul_le_mul hl2.le hq hq0 (by norm_num)
  rcases lt_or_ge S 1000000 with hS6 | hS6
  · have hK2z : K2 = 0 := Nat.floor_eq_zero.mpr (by linarith)
    rw [hK2z] at h2
    simp only [Nat.cast_zero, zero_mul, mul_zero, Real.sqrt_zero, add_zero] at h2
    have hM := hlogX (1.05 / 10001 + 1.05 / 100000) (by linarith)
    have hP : 47734020.6 / S ^ 2 ≤ 0.00477340206 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  · have hK2 : (K2 : ℝ) ≤ (S / 1000000 + 1) / 2 := Nat.floor_le (by positivity)
    have hsq : Real.sqrt (S / 1000000) * Real.sqrt (2 * (K2 : ℝ)) ≤ S / 1000000 + 1 / 2 := by
      have hp := Real.sq_sqrt (show (0 : ℝ) ≤ S / 1000000 by positivity)
      have hq := Real.sq_sqrt (show (0 : ℝ) ≤ 2 * (K2 : ℝ) by positivity)
      nlinarith [sq_nonneg (Real.sqrt (S / 1000000) - Real.sqrt (2 * (K2 : ℝ)))]
    have hsq' : 2 * 817.168 * Real.sqrt (S / 1000000) * Real.sqrt (2 * (K2 : ℝ)) ≤
        2 * 817.168 * (S / 1000000 + 1 / 2) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hsq (by norm_num)
    have hc : (1634.34 + 817.168 * 11.98 : ℝ) = 11424.01264 := by norm_num
    rw [hc] at h2
    have hM := hlogX (1.05 / 10001 + 1.05 / 1000000 + 0.01142401264 + 0.002451504)
      (by linarith)
    have hP : 47734020.6 / S ^ 2 ≤ 0.0000477340206 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    linarith

end Principia.Common.TernaryGoldbach.M2L
