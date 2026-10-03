/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.SmoothPP

set_option autoImplicit false

/-!
# Link 1 of the smoothed spine, DISCHARGED for every pair of summable weights

`Smoothed.lean` reduces `Principia.Erdos1054.Cite_Helfgott_weighted` to Platt plus six named
links; `SmoothPP.lean` removed `PrimePowerSmooth` (at a `(log H)²` constant). This file **proves
`Smooth.CircleIdSmooth` (7.49) from `Smooth.Summ` alone** and re-proves the composition with both
generic links gone:

  `cite_of_smooth4 : PlattGRH → SupBounds → Summ → MajorLowerSmooth → MinorUpperSmooth →
      Cite_Helfgott_weighted`
  `cite4_no_summ   : PlattGRH → SupBounds → MajorLowerSmooth → MinorUpperSmooth →
      Cite_Helfgott_weighted`

The two remaining links are Helfgott's two papers (major arcs with Platt, minor arcs); both are
OPEN, and nothing here proves any part of ternary Goldbach.

## The side condition, and why it is the right one

`circleId_all` holds for **every** `N : ℕ` and **every** scale `x : ℝ` (no parity, size or sign
hypothesis) as soon as `n ↦ Λ(n)|ηp(n/x)|` and `n ↦ Λ(n)|ηs(n/x)|` are summable. `Summ` supplies
exactly that at `x = helfgottX N` for odd `N ≥ 10^27`, so `circleId_of_summ : Summ → CircleIdSmooth`
uses nothing else. It cannot be dropped for arbitrary weights: without it `smSum` is Mathlib's junk
`0` (`Smooth.smSum_junk`), the right side of (7.49) is `0`, and the left side need not be. In the
composition it costs nothing, because `Smooth.summ_of_major` derives `Summ` from Platt and the
major-arc link, which is how `cite4_no_summ` drops it.

## The proof

1. **Coefficients.** `smSum η x α = ser (coef η x) α` **by `rfl`**, where
   `ser c α = ∑' n, c n e(nα)` and `coef η x n = Λ(n) η(n/x)`; `‖coef η x n‖ = Λ(n)|η(n/x)|`, so
   `Summ` is absolute summability of the coefficients.
2. **Cauchy product** (`ser_mul`). For absolutely summable `c`, `d`: `ser c · ser d = ser (c ⋆ d)`,
   `(c ⋆ d)(n) = ∑_{k+l=n} c k d l`, from Mathlib's
   `tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm` plus `e(kα)e(lα) = e(nα)` on the
   antidiagonal; `c ⋆ d` is again absolutely summable
   (`summable_norm_sum_mul_antidiagonal_of_summable_norm`). Applied twice, `S_{η₊}²S_{η_*} =
   ser (a ⋆ (a ⋆ b))` (`kernS_eq`). This replaces `CircleMethod.sum_cube`.
3. **Interchange and orthogonality** (`integral_ser`). `∫_{(0,1]} ser c(α) e(−Nα) dα = c N`:
   Mathlib's `integral_tsum_of_summable_integral_norm` (each term has integral-norm `‖c n‖`) swaps
   `∑'` and `∫`, and `MinorArc.integral_e` at `k = n − N ∈ ℤ` kills every `n ≠ N`
   (`integral_term`). This replaces `integral_finsetSum`.
4. **Reindexing** (`reindex`). `(a ⋆ (a ⋆ b))(N) = ∑_{p<N} ∑_{q<N} [p+q<N] a p a q b(N−p−q)`, the
   index set and natural subtraction of `tripleW` verbatim. **Only `b 0 = 0` is used**, twice: the
   outer index `p = N` contributes `a N · a 0 · b 0`, and for `p < N` the inner index `q = N − p`
   contributes `a(N−p) · b 0`. Every other mismatch between the antidiagonal and `range N × range N`
   is absorbed by the guard `p + q < N` (`filter_lt`). For `b = coef ηs x`, `b 0 = Λ 0 · … = 0`.
   So the weights change nothing about the two vanishing mechanisms `CircleMethod` found.

**The identity is TRUE as stated in `CircleIdSmooth`**: no off-by-one, and the `n = 0` term of
`smSum` is harmless (`Λ 0 = 0`). The statement did not need weakening anywhere.

## Non-vacuity (the adversarial pass)

`circleId_of_summ` introduces no new `Prop`; it removes one. The attack on an identity is "both
sides are identically zero", or "the hypothesis is never met". Both are refuted by theorems:

* **`Summ` is met by a nonzero pair** — the compactly supported indicator `box = 1_{[0,1]}`
  (`summ_box`, finitely many nonzero terms at every positive scale) — **and by a weight that is NOT
  compactly supported**, `expo u = e^{−|u|}` (`summ_expo`, via `Λ(n) ≤ n` and
  `Real.summable_pow_mul_exp_neg_nat_mul`). Helfgott's `η₊`, `η_*` are not compactly supported
  either, so the second witness is the relevant one: `Summ` is not a disguised compact-support
  assumption.
* **Both sides are genuinely nonzero** at `N = 3^57` (odd, `≈ 1.57·10^27 ≥ 10^27`) for `box, box`:
  `tripleW_box_pos` exhibits the positive summand `p = q = N − p − q = 3^56` (`Λ(3^56) = log 3`,
  `3^56/x ≤ 989/1470 ≤ 1`) over nonnegative summands, and `integral_box_pos` transfers it through
  the identity to `0 < Re ∫_{(0,1]} S_box² S_box e(−Nα) dα`.
* **The weight genuinely bites**: `box_cuts` shows `box((N−1)/x) = 0` at the same `N` (because
  `helfgottX N ≤ N/2`), so on the index set of `tripleW` the witness is not the constant `1`, and
  the identity proved is not `CircleMethod.circleMethodIdentity_holds` in disguise. (On the right
  side the frequencies of `S_box` stop at `n ≤ x ≈ 0.4955 N`; for `expo` they never stop.)

## A side finding, from the same witness

`PrimePower.lean` and `GatePrimePower.lean` say that refuting `Spine.PrimePowerRemoval 0` needs an
odd `H ≥ 10^27` with a prime-power representation "not constructible without a ternary-Goldbach-type
input". `3^57 = 3^56 + 3^56 + 3^56` is one. `ppRemoval_zero_false` proves
`¬ Spine.PrimePowerRemoval 0`, so the sharp spine's removal constant must be positive: that note's
"argued, not proved" is now proved. (Those files are not edited here.)
-/

namespace Principia.Common.TernaryGoldbach.SmCI

open ArithmeticFunction MeasureTheory Principia.Common.Goldbach
open scoped ArithmeticFunction
open Principia.Common.TernaryGoldbach.Smooth
open Principia.Erdos1054 (helfgottX Cite_Helfgott_weighted)

/-! ## Trigonometric series with absolutely summable coefficients -/

/-- **The series `∑' n, c n · e(nα)`**, an infinite sum over `n : ℕ`. -/
noncomputable def ser (c : ℕ → ℂ) (α : ℝ) : ℂ :=
  ∑' n : ℕ, c n * e ((n : ℝ) * α)

/-- **Additive convolution** `(c ⋆ d)(n) = ∑_{k+l=n} c k · d l` (the Cauchy product's coefficient).
-/
noncomputable def conv (c d : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ kl ∈ Finset.antidiagonal n, c kl.1 * d kl.2

/-- `‖c n · e(nα)‖ = ‖c n‖`. -/
theorem norm_ser_term (c : ℕ → ℂ) (α : ℝ) (n : ℕ) : ‖c n * e ((n : ℝ) * α)‖ = ‖c n‖ := by
  rw [norm_mul, e_norm, mul_one]

/-- The convolution of absolutely summable sequences is absolutely summable. -/
theorem summable_conv (c d : ℕ → ℂ) (hc : Summable fun n => ‖c n‖)
    (hd : Summable fun n => ‖d n‖) : Summable fun n => ‖conv c d n‖ :=
  summable_norm_sum_mul_antidiagonal_of_summable_norm hc hd

/-- **The Cauchy product**: `ser c · ser d = ser (c ⋆ d)` for absolutely summable `c`, `d`. -/
theorem ser_mul (c d : ℕ → ℂ) (hc : Summable fun n => ‖c n‖)
    (hd : Summable fun n => ‖d n‖) (α : ℝ) : ser c α * ser d α = ser (conv c d) α := by
  have hc' : Summable fun n : ℕ => ‖c n * e ((n : ℝ) * α)‖ :=
    hc.congr fun n => (norm_ser_term c α n).symm
  have hd' : Summable fun n : ℕ => ‖d n * e ((n : ℝ) * α)‖ :=
    hd.congr fun n => (norm_ser_term d α n).symm
  unfold ser
  rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hc' hd']
  refine tsum_congr fun n => ?_
  rw [conv, Finset.sum_mul]
  refine Finset.sum_congr rfl fun kl hkl => ?_
  have hk : kl.1 + kl.2 = n := Finset.mem_antidiagonal.mp hkl
  have he : e ((kl.1 : ℝ) * α) * e ((kl.2 : ℝ) * α) = e ((n : ℝ) * α) := by
    rw [e_add, ← hk]
    congr 1
    push_cast
    ring
  rw [← he]
  ring

/-! ## Interchange of `∑'` and `∫`, and orthogonality -/

/-- **Orthogonality on `(0,1]`**: `∫_{(0,1]} e(nα) e(−Nα) dα = [n = N]`. -/
theorem integral_term (N n : ℕ) :
    ∫ α in Set.Ioc (0 : ℝ) 1, e ((n : ℝ) * α) * e (-(N : ℝ) * α) = if n = N then 1 else 0 := by
  have h : ∀ α : ℝ, e ((n : ℝ) * α) * e (-(N : ℝ) * α)
      = e ((((n : ℤ) - (N : ℤ) : ℤ) : ℝ) * α) := by
    intro α
    rw [e_add]
    congr 1
    push_cast
    ring
  simp_rw [h]
  rw [← intervalIntegral.integral_of_le (zero_le_one' ℝ), MinorArc.integral_e]
  by_cases hn : n = N
  · rw [if_pos (by omega), if_pos hn]
  · rw [if_neg (by omega), if_neg hn]

/-- **Coefficient extraction**: `∫_{(0,1]} ser c(α) e(−Nα) dα = c N` for absolutely summable `c`.
The interchange is `integral_tsum_of_summable_integral_norm`; each term has integral-norm
`‖c n‖`. -/
theorem integral_ser (c : ℕ → ℂ) (hc : Summable fun n => ‖c n‖) (N : ℕ) :
    ∫ α in Set.Ioc (0 : ℝ) 1, ser c α * e (-(N : ℝ) * α) = c N := by
  have hpt : ∀ α : ℝ, ser c α * e (-(N : ℝ) * α)
      = ∑' n : ℕ, c n * (e ((n : ℝ) * α) * e (-(N : ℝ) * α)) := by
    intro α
    rw [ser, ← tsum_mul_right]
    refine tsum_congr fun n => ?_
    ring
  have hcont : ∀ n : ℕ, Continuous fun α : ℝ => c n * (e ((n : ℝ) * α) * e (-(N : ℝ) * α)) :=
    fun n => continuous_const.mul
      ((Spine.continuous_e.comp (continuous_const.mul continuous_id)).mul
        (Spine.continuous_e.comp (continuous_const.mul continuous_id)))
  have hint : ∀ n : ℕ, Integrable (fun α : ℝ => c n * (e ((n : ℝ) * α) * e (-(N : ℝ) * α)))
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) := fun n => (hcont n).integrableOn_Ioc
  have hnorm : ∀ n : ℕ,
      ∫ α in Set.Ioc (0 : ℝ) 1, ‖c n * (e ((n : ℝ) * α) * e (-(N : ℝ) * α))‖ = ‖c n‖ := by
    intro n
    simp only [norm_mul, e_norm, mul_one]
    rw [setIntegral_const, Real.volume_real_Ioc_of_le (zero_le_one' ℝ)]
    simp
  have hsum : Summable fun n : ℕ =>
      ∫ α in Set.Ioc (0 : ℝ) 1, ‖c n * (e ((n : ℝ) * α) * e (-(N : ℝ) * α))‖ :=
    hc.congr fun n => (hnorm n).symm
  simp_rw [hpt]
  rw [← integral_tsum_of_summable_integral_norm hint hsum]
  have hterm : ∀ n : ℕ, ∫ α in Set.Ioc (0 : ℝ) 1, c n * (e ((n : ℝ) * α) * e (-(N : ℝ) * α))
      = if n = N then c n else 0 := by
    intro n
    rw [integral_const_mul, integral_term]
    split_ifs <;> simp
  simp_rw [hterm]
  rw [tsum_eq_single N (fun n hn => if_neg hn), if_pos rfl]

/-! ## The reindexing -/

/-- The convolution over `range`, with natural subtraction. -/
theorem conv_eq_range (c d : ℕ → ℂ) (n : ℕ) :
    conv c d n = ∑ k ∈ Finset.range (n + 1), c k * d (n - k) :=
  Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun k l => c k * d l) n

/-- The guard `p + q < N` cuts `range N` down to `range (N − p)`. -/
theorem filter_lt (N p : ℕ) :
    (Finset.range N).filter (fun q => p + q < N) = Finset.range (N - p) := by
  ext q
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

/-- **The reindexing.** `(a ⋆ (a ⋆ b))(N)` is the guarded double sum over `range N × range N` with
third coordinate `N − p − q`, the shape of `tripleW`. Only `b 0 = 0` is used. -/
theorem reindex (a b : ℕ → ℂ) (hb : b 0 = 0) (N : ℕ) :
    conv a (conv a b) N = ∑ p ∈ Finset.range N, ∑ q ∈ Finset.range N,
      (if p + q < N then a p * a q * b (N - p - q) else 0) := by
  rw [conv_eq_range, Finset.sum_range_succ, Nat.sub_self, conv_eq_range, zero_add,
    Finset.sum_range_one, hb, mul_zero, mul_zero, add_zero]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hpN : p < N := Finset.mem_range.mp hp
  rw [← Finset.sum_filter, filter_lt, conv_eq_range, Finset.sum_range_succ,
    show N - p - (N - p) = 0 by omega, hb, mul_zero, add_zero, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  ring

/-! ## LINK 1, DISCHARGED -/

/-- **The coefficients of `smSum`**: `Λ(n)·η(n/x)`. -/
noncomputable def coef (η : ℝ → ℝ) (x : ℝ) (n : ℕ) : ℂ :=
  ((Λ n : ℝ) : ℂ) * ((η ((n : ℝ) / x) : ℝ) : ℂ)

/-- `smSum` is the series with coefficients `coef`, **definitionally**. -/
theorem smSum_eq (η : ℝ → ℝ) (x α : ℝ) : smSum η x α = ser (coef η x) α := rfl

/-- `‖coef η x n‖ = Λ(n)|η(n/x)|`, the summand of `Summ`. -/
theorem norm_coef (η : ℝ → ℝ) (x : ℝ) (n : ℕ) : ‖coef η x n‖ = Λ n * |η ((n : ℝ) / x)| := by
  rw [coef, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg vonMangoldt_nonneg]

/-- `coef η x 0 = 0`, because `Λ 0 = 0`: the one fact `reindex` needs. -/
theorem coef_zero (η : ℝ → ℝ) (x : ℝ) : coef η x 0 = 0 := by
  simp [coef]

/-- **The integrand of (7.49) as one series**: `S_{η₊}² S_{η_*} e(−Nα) = ser (a ⋆ (a ⋆ b))(α)
e(−Nα)` with `a = coef ηp x`, `b = coef ηs x`. -/
theorem kernS_eq (ηp ηs : ℝ → ℝ) (N : ℕ) (x : ℝ)
    (hp : Summable fun n => ‖coef ηp x n‖) (hs : Summable fun n => ‖coef ηs x n‖) (α : ℝ) :
    kernS ηp ηs N x α
      = ser (conv (coef ηp x) (conv (coef ηp x) (coef ηs x))) α * e (-(N : ℝ) * α) := by
  have h : kernS ηp ηs N x α = ser (coef ηp x) α * (ser (coef ηp x) α * ser (coef ηs x) α)
      * e (-(N : ℝ) * α) := by
    rw [kernS, smSum_eq, smSum_eq]
    ring
  rw [h, ser_mul _ _ hp hs, ser_mul _ _ hp (summable_conv _ _ hp hs)]

/-- **(7.49) at every `N` and every scale `x`**, from absolute summability of the two weights at
that scale. No parity, size or sign hypothesis. -/
theorem circleId_all (ηp ηs : ℝ → ℝ) (N : ℕ) (x : ℝ)
    (hp : Summable fun n : ℕ => Λ n * |ηp ((n : ℝ) / x)|)
    (hs : Summable fun n : ℕ => Λ n * |ηs ((n : ℝ) / x)|) :
    ((tripleW ηp ηs N x : ℝ) : ℂ) = ∫ α in Set.Ioc (0 : ℝ) 1, kernS ηp ηs N x α := by
  have hp' : Summable fun n => ‖coef ηp x n‖ := hp.congr fun n => (norm_coef ηp x n).symm
  have hs' : Summable fun n => ‖coef ηs x n‖ := hs.congr fun n => (norm_coef ηs x n).symm
  simp_rw [kernS_eq ηp ηs N x hp' hs']
  rw [integral_ser _ (summable_conv _ _ hp' (summable_conv _ _ hp' hs')) N,
    reindex _ _ (coef_zero ηs x) N, tripleW, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  split_ifs
  · simp only [coef]
    push_cast
    ring
  · simp

/-- **Link 1 of `Smoothed.lean` is a theorem, for every pair of summable weights**: `Summ` implies
`CircleIdSmooth`. `Summ` is used for nothing but the two summabilities at `x = helfgottX N`. -/
theorem circleId_of_summ (ηp ηs : ℝ → ℝ) (sm : Summ ηp ηs) : CircleIdSmooth ηp ηs :=
  fun N hodd hN => circleId_all ηp ηs N (helfgottX N) (sm N hodd hN).1 (sm N hodd hN).2

/-! ## THE SPINE, WITH FOUR LINKS -/

/-- **`Smooth.cite_of_smooth` with BOTH generic links removed**: `PrimePowerSmooth` (by
`SmPP.pp_crude`, inside `SmPP.cite_of_smooth5`) and `CircleIdSmooth` (by `circleId_of_summ`).
What is left is Platt, the sup norms, summability, and Helfgott's two papers. -/
theorem cite_of_smooth4 (ηp ηs : ℝ → ℝ) (grh : Spine.PlattGRH) (sb : SupBounds ηp ηs)
    (sm : Summ ηp ηs) (mj : MajorLowerSmooth ηp ηs) (mn : MinorUpperSmooth ηp ηs) :
    Cite_Helfgott_weighted :=
  SmPP.cite_of_smooth5 ηp ηs grh sb sm (circleId_of_summ ηp ηs sm) mj mn

/-- **Platt plus three links**: `Summ` is supplied by `Smooth.summ_of_major`. -/
theorem cite4_no_summ (ηp ηs : ℝ → ℝ) (grh : Spine.PlattGRH) (sb : SupBounds ηp ηs)
    (mj : MajorLowerSmooth ηp ηs) (mn : MinorUpperSmooth ηp ηs) : Cite_Helfgott_weighted :=
  cite_of_smooth4 ηp ηs grh sb (summ_of_major ηp ηs grh mj) mj mn

/-- The existential form, one weight pair for all `N`, with the four remaining hypotheses. -/
theorem cite_of_smooth4_ex (grh : Spine.PlattGRH)
    (links : ∃ ηp ηs : ℝ → ℝ, SupBounds ηp ηs ∧ MajorLowerSmooth ηp ηs ∧
      MinorUpperSmooth ηp ηs) : Cite_Helfgott_weighted := by
  obtain ⟨ηp, ηs, sb, mj, mn⟩ := links
  exact cite4_no_summ ηp ηs grh sb mj mn

/-! ## Non-vacuity -/

/-- A weight vanishing beyond `R` gives a finitely supported, hence summable, `Λ(n)|η(n/x)|` at
every positive scale. -/
theorem summable_of_vanish (η : ℝ → ℝ) (R x : ℝ) (hx : 0 < x) (hη : ∀ u, R < u → η u = 0) :
    Summable fun n : ℕ => Λ n * |η ((n : ℝ) / x)| := by
  refine summable_of_ne_finset_zero (s := Finset.range (⌊R * x⌋₊ + 1)) fun n hn => ?_
  rw [Finset.mem_range, not_lt] at hn
  have h1 : R * x < (n : ℝ) := Nat.lt_of_floor_lt (by omega)
  have h2 : R < (n : ℝ) / x := by
    rw [lt_div_iff₀ hx]
    exact h1
  rw [hη _ h2, abs_zero, mul_zero]

/-- **The compactly supported witness**: the indicator of `[0, 1]`. -/
noncomputable def box (u : ℝ) : ℝ := if 0 ≤ u ∧ u ≤ 1 then 1 else 0

theorem box_nonneg (u : ℝ) : 0 ≤ box u := by
  unfold box
  split_ifs <;> norm_num

/-- **`Summ` is met by a nonzero pair**: `box, box`. -/
theorem summ_box : Summ box box := by
  intro N _ hN
  have hx : 0 < helfgottX N := helfX_pos N (lt_of_lt_of_le (by norm_num) hN)
  have hv : ∀ u : ℝ, 1 < u → box u = 0 := fun u hu => by
    unfold box
    rw [if_neg (by intro h; linarith [h.2])]
  exact ⟨summable_of_vanish box 1 _ hx hv, summable_of_vanish box 1 _ hx hv⟩

/-- **The non-compactly-supported witness**: `u ↦ e^{−|u|}`, positive everywhere. -/
noncomputable def expo (u : ℝ) : ℝ := Real.exp (-|u|)

/-- **`Summ` does not force compact support**: `expo, expo` satisfies it, via `Λ(n) ≤ n` and
`∑ n e^{−n/x} < ∞`. -/
theorem summ_expo : Summ expo expo := by
  intro N _ hN
  have hx : 0 < helfgottX N := helfX_pos N (lt_of_lt_of_le (by norm_num) hN)
  have hS : Summable fun n : ℕ => Λ n * |expo ((n : ℝ) / helfgottX N)| := by
    refine (Real.summable_pow_mul_exp_neg_nat_mul 1 (inv_pos.mpr hx)).of_nonneg_of_le
      (fun n => mul_nonneg vonMangoldt_nonneg (abs_nonneg _)) fun n => ?_
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hq : (0 : ℝ) ≤ (n : ℝ) / helfgottX N := div_nonneg hn0 hx.le
    have hΛ : Λ n ≤ (n : ℝ) := le_trans vonMangoldt_le_log (Real.log_le_self hn0)
    have hE : |expo ((n : ℝ) / helfgottX N)| = Real.exp (-(helfgottX N)⁻¹ * (n : ℝ)) := by
      rw [expo, abs_of_pos (Real.exp_pos _), abs_of_nonneg hq, div_eq_inv_mul]
      ring_nf
    rw [hE, pow_one]
    exact mul_le_mul_of_nonneg_right hΛ (Real.exp_pos _).le
  exact ⟨hS, hS⟩

/-- `helfgottX N ≤ N/2`: the denominator `2 + 9/(196√(2π))` exceeds `2`. -/
theorem helfX_le_half (N : ℕ) : helfgottX N ≤ (N : ℝ) / 2 := by
  rw [Principia.Erdos1054.helfgottX]
  refine div_le_div_of_nonneg_left (Nat.cast_nonneg N) (by norm_num) ?_
  have : (0 : ℝ) ≤ 9 / (196 * Real.sqrt (2 * Real.pi)) := by positivity
  linarith

/-- **Both sides of (7.49) are nonzero somewhere**: `tripleW box box N x > 0` at `N = 3^57`
(odd, `≥ 10^27`), from the summand `p = q = N − p − q = 3^56`. -/
theorem tripleW_box_pos : 0 < tripleW box box (3 ^ 57) (helfgottX (3 ^ 57)) := by
  set x := helfgottX (3 ^ 57) with hxdef
  have hxge : (490 : ℝ) / 989 * ((3 ^ 57 : ℕ) : ℝ) ≤ x := helfX_ge (3 ^ 57)
  have hx : 0 < x := helfX_pos (3 ^ 57) (by positivity)
  have hb1 : box (((3 ^ 56 : ℕ) : ℝ) / x) = 1 := by
    unfold box
    refine if_pos ⟨by positivity, ?_⟩
    rw [div_le_one hx]
    push_cast at hxge ⊢
    linarith
  have hsub : 3 ^ 57 - 3 ^ 56 - 3 ^ 56 = 3 ^ 56 := by norm_num
  have hlt : 3 ^ 56 + 3 ^ 56 < 3 ^ 57 := by norm_num
  have hΛ : Λ (3 ^ 56) = Real.log 3 := by
    rw [vonMangoldt_apply_pow (by norm_num), vonMangoldt_apply_prime Nat.prime_three]
    norm_num
  have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hnn : ∀ p q : ℕ, 0 ≤ (if p + q < 3 ^ 57 then Λ p * Λ q * Λ (3 ^ 57 - p - q) *
      box ((p : ℝ) / x) * box ((q : ℝ) / x) * box (((3 ^ 57 - p - q : ℕ) : ℝ) / x) else 0) := by
    intro p q
    split_ifs
    · have h1 := box_nonneg ((p : ℝ) / x)
      have h2 := box_nonneg ((q : ℝ) / x)
      have h3 := box_nonneg (((3 ^ 57 - p - q : ℕ) : ℝ) / x)
      have h4 : (0 : ℝ) ≤ Λ p := vonMangoldt_nonneg
      have h5 : (0 : ℝ) ≤ Λ q := vonMangoldt_nonneg
      have h6 : (0 : ℝ) ≤ Λ (3 ^ 57 - p - q) := vonMangoldt_nonneg
      exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg h4 h5) h6) h1) h2) h3
    · exact le_refl 0
  have hmem : 3 ^ 56 ∈ Finset.range (3 ^ 57) := Finset.mem_range.mpr (by norm_num)
  have hpos : 0 < (if 3 ^ 56 + 3 ^ 56 < 3 ^ 57 then Λ (3 ^ 56) * Λ (3 ^ 56) *
      Λ (3 ^ 57 - 3 ^ 56 - 3 ^ 56) * box (((3 ^ 56 : ℕ) : ℝ) / x) *
      box (((3 ^ 56 : ℕ) : ℝ) / x) * box (((3 ^ 57 - 3 ^ 56 - 3 ^ 56 : ℕ) : ℝ) / x) else 0) := by
    rw [if_pos hlt, hsub, hΛ, hb1]
    positivity
  unfold tripleW
  refine lt_of_lt_of_le hpos (le_trans ?_ (Finset.single_le_sum
    (f := fun p => ∑ q ∈ Finset.range (3 ^ 57), (if p + q < 3 ^ 57 then Λ p * Λ q *
      Λ (3 ^ 57 - p - q) * box ((p : ℝ) / x) * box ((q : ℝ) / x) *
      box (((3 ^ 57 - p - q : ℕ) : ℝ) / x) else 0))
    (fun p _ => Finset.sum_nonneg fun q _ => hnn p q) hmem))
  exact Finset.single_le_sum (f := fun q => (if 3 ^ 56 + q < 3 ^ 57 then Λ (3 ^ 56) * Λ q *
      Λ (3 ^ 57 - 3 ^ 56 - q) * box (((3 ^ 56 : ℕ) : ℝ) / x) * box ((q : ℝ) / x) *
      box (((3 ^ 57 - 3 ^ 56 - q : ℕ) : ℝ) / x) else 0))
    (fun q _ => hnn (3 ^ 56) q) hmem

/-- **… and so is the circle integral**, through the identity: `0 < Re ∫_{(0,1]} S_box² S_box
e(−Nα) dα` at `N = 3^57`. A genuine consequence of `circleId_of_summ`, not a restatement. -/
theorem integral_box_pos :
    0 < (∫ α in Set.Ioc (0 : ℝ) 1, kernS box box (3 ^ 57) (helfgottX (3 ^ 57)) α).re := by
  have hodd : Odd (3 ^ 57 : ℕ) := Odd.pow ⟨1, by norm_num⟩
  rw [← circleId_of_summ box box summ_box (3 ^ 57) hodd (by norm_num), Complex.ofReal_re]
  exact tripleW_box_pos

/-- **The witness weight is not constant on the index set**: `box((N − 1)/x) = 0` at `N = 3^57`,
since `x ≤ N/2`. So `tripleW box box` is a genuinely weighted sum there, not `lambdaTriple`. -/
theorem box_cuts : box (((3 ^ 57 - 1 : ℕ) : ℝ) / helfgottX (3 ^ 57)) = 0 := by
  set x := helfgottX (3 ^ 57) with hxdef
  have hx : 0 < x := helfX_pos (3 ^ 57) (by positivity)
  have hle : x ≤ ((3 ^ 57 : ℕ) : ℝ) / 2 := helfX_le_half (3 ^ 57)
  unfold box
  refine if_neg fun h => ?_
  have h2 := h.2
  rw [div_le_one hx] at h2
  have hc : ((3 ^ 57 - 1 : ℕ) : ℝ) = ((3 ^ 57 : ℕ) : ℝ) - 1 := by
    rw [Nat.cast_sub (Nat.one_le_pow _ _ (by norm_num)), Nat.cast_one]
  rw [hc] at h2
  push_cast at hle h2
  linarith

/-! ## A side finding: the sharp removal link needs a POSITIVE constant

`PrimePower.lean` (its closing note) and `GatePrimePower.lean` record that refuting
`Spine.PrimePowerRemoval 0` "needs an odd `H ≥ 10^27` with a prime-power representation, which is
not constructible without a ternary-Goldbach-type input", so that the necessity of `cPP > 0` was
"argued, not proved". The witness above refutes that: `3^57 = 3^56 + 3^56 + 3^56` is such a
representation, and `3^56` is not prime, so that summand is in `lambdaTriple` and not in
`ternaryLogCount`. -/

/-- One summand of `lambdaTriple` minus the matching summand of `ternaryLogCount` is `≥ 0`. -/
theorem gap_nonneg (H p q : ℕ) :
    0 ≤ (if p + q < H then Λ p * Λ q * Λ (H - p - q) else 0)
      - (if p + q < H ∧ p.Prime ∧ q.Prime ∧ (H - p - q).Prime ∧ Odd p ∧ Odd q ∧ Odd (H - p - q)
          then Real.log p * Real.log q * Real.log ((H - p - q : ℕ) : ℝ) else 0) := by
  by_cases hc : p + q < H ∧ p.Prime ∧ q.Prime ∧ (H - p - q).Prime ∧ Odd p ∧ Odd q ∧
      Odd (H - p - q)
  · rw [if_pos hc, if_pos hc.1, vonMangoldt_apply_prime hc.2.1, vonMangoldt_apply_prime hc.2.2.1,
      vonMangoldt_apply_prime hc.2.2.2.1, sub_self]
  · rw [if_neg hc, sub_zero]
    split
    · exact mul_nonneg (mul_nonneg vonMangoldt_nonneg vonMangoldt_nonneg) vonMangoldt_nonneg
    · exact le_refl 0

/-- **`PrimePowerRemoval 0` is FALSE**: at `H = 3^57`, `lambdaTriple H ≥ ternaryLogCount H +
(log 3)³`. So the removal link of the sharp spine genuinely constrains: its constant must be
positive. (Proved, where the library previously said it could only be argued.) -/
theorem ppRemoval_zero_false : ¬ Spine.PrimePowerRemoval 0 := by
  intro h
  have h1 := h (3 ^ 57) (Odd.pow ⟨1, by norm_num⟩) (by norm_num)
  rw [zero_mul, zero_mul, sub_zero] at h1
  have hsub : 3 ^ 57 - 3 ^ 56 - 3 ^ 56 = 3 ^ 56 := by norm_num
  have hlt : 3 ^ 56 + 3 ^ 56 < 3 ^ 57 := by norm_num
  have hΛ : Λ (3 ^ 56) = Real.log 3 := by
    rw [vonMangoldt_apply_pow (by norm_num), vonMangoldt_apply_prime Nat.prime_three]
    norm_num
  have hnp : ¬ (3 ^ 56).Prime := Nat.Prime.not_prime_pow (by norm_num)
  have hmem : 3 ^ 56 ∈ Finset.range (3 ^ 57) := Finset.mem_range.mpr (by norm_num)
  have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hdiff : Real.log 3 * Real.log 3 * Real.log 3
      ≤ Spine.lambdaTriple (3 ^ 57) - ternaryLogCount (3 ^ 57) := by
    rw [Spine.lambdaTriple, ternaryLogCount, ← Finset.sum_sub_distrib]
    refine le_trans ?_ (Finset.single_le_sum (fun p _ => ?_) hmem)
    · rw [← Finset.sum_sub_distrib]
      refine le_trans ?_ (Finset.single_le_sum (fun q _ => gap_nonneg _ _ q) hmem)
      rw [if_pos hlt, if_neg (fun hc => hnp hc.2.1), hsub, hΛ, sub_zero]
    · rw [← Finset.sum_sub_distrib]
      exact Finset.sum_nonneg fun q _ => gap_nonneg _ p q
  have hpos : 0 < Real.log 3 * Real.log 3 * Real.log 3 := by positivity
  linarith

end Principia.Common.TernaryGoldbach.SmCI
