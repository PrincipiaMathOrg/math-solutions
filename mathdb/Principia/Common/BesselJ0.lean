import Mathlib

set_option autoImplicit false

/-!
# The Bessel function `J₀`, by its power series, and its alternating bracket

Mathlib has **no Bessel function of any kind** (re-grepped 2026-09-25: every `bessel` hit is
Bessel's *inequality*).  This file defines `J₀` by its series and proves the one analytic fact a
rational certificate about it needs:

    besselP 13 z  <=  J0 z  <=  besselP 12 z      for 0 <= z <= 6,

where `besselP N` is the partial sum through `k = N`.  Everything else such a certificate wants is
then arithmetic on a polynomial with rational coefficients.

**Why the head splits off.**  Mathlib's alternating-series bounds
(`Antitone.alternating_series_le_tendsto`, `Antitone.tendsto_le_alternating_series`) require the
term sequence to be antitone *everywhere*, and `jterm z k = (z^2/4)^k / (k!)^2` is not: the ratio
`jterm z (k+1) / jterm z k = (z^2/4)/(k+1)^2` exceeds `1` for small `k` when `z > 2`.  It is at most
`1` once `2(k+1) >= z`, so for `z <= 6` the sequence is antitone from `k = 2` on.  The first two
terms are therefore separated by `Summable.sum_add_tsum_nat_add`, the bounds are applied to the
shifted tail, and the head is added back.  The shift costs nothing in signs because
`(-1)^(j+2) = (-1)^j`.

Nothing here mentions any campaign's objects.
-/

namespace Principia.Common

open Finset Filter Topology

/-- The modulus of the `k`-th term of the `J₀` series: `(z^2/4)^k / (k!)^2`. -/
noncomputable def jterm (z : ℝ) (k : ℕ) : ℝ := (z ^ 2 / 4) ^ k / (Nat.factorial k : ℝ) ^ 2

/-- The Bessel function of the first kind of order zero, by its power series. -/
noncomputable def J0 (z : ℝ) : ℝ := ∑' k, (-1 : ℝ) ^ k * jterm z k

/-- `besselP N z` is the partial sum of the `J₀` series through `k = N`. -/
noncomputable def besselP (N : ℕ) (z : ℝ) : ℝ := ∑ k ∈ range (N + 1), (-1 : ℝ) ^ k * jterm z k

/-- The partial sum as a polynomial in `u = z^2/4`.  Every sign question about `besselP` is a
question about `bpoly` at HALF the degree, which is what makes a one-piece Bernstein certificate
affordable. -/
noncomputable def bpoly (N : ℕ) (u : ℝ) : ℝ :=
  ∑ k ∈ range (N + 1), (-1 : ℝ) ^ k * u ^ k / (Nat.factorial k : ℝ) ^ 2

theorem besselP_eq_bpoly (N : ℕ) (z : ℝ) : besselP N z = bpoly N (z ^ 2 / 4) := by
  unfold besselP bpoly jterm
  exact Finset.sum_congr rfl fun k _ => by ring

theorem jterm_nonneg (z : ℝ) (k : ℕ) : 0 ≤ jterm z k := by
  unfold jterm
  have h : (0 : ℝ) < (Nat.factorial k : ℝ) ^ 2 := by
    have : (0 : ℝ) < (Nat.factorial k : ℝ) := by exact_mod_cast Nat.factorial_pos k
    positivity
  have h2 : (0 : ℝ) ≤ (z ^ 2 / 4) ^ k := by positivity
  exact div_nonneg h2 h.le

theorem jterm_le_pow_div_factorial (z : ℝ) (k : ℕ) :
    jterm z k ≤ (z ^ 2 / 4) ^ k / (Nat.factorial k : ℝ) := by
  unfold jterm
  have hpos : 0 < Nat.factorial k := Nat.factorial_pos k
  have h1 : (1 : ℝ) ≤ (Nat.factorial k : ℝ) := by exact_mod_cast hpos
  have h0 : (0 : ℝ) < (Nat.factorial k : ℝ) := by linarith
  have hsq : (Nat.factorial k : ℝ) ≤ (Nat.factorial k : ℝ) ^ 2 := by nlinarith
  have hnum : (0 : ℝ) ≤ (z ^ 2 / 4) ^ k := by positivity
  gcongr

theorem summable_jterm (z : ℝ) : Summable (jterm z) :=
  Summable.of_nonneg_of_le (jterm_nonneg z) (jterm_le_pow_div_factorial z)
    (Real.summable_pow_div_factorial _)

theorem summable_jterm_alt (z : ℝ) : Summable (fun k => (-1 : ℝ) ^ k * jterm z k) := by
  refine Summable.of_norm ?_
  have h : (fun k => ‖(-1 : ℝ) ^ k * jterm z k‖) = jterm z := by
    funext k
    rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
      Real.norm_eq_abs, abs_of_nonneg (jterm_nonneg z k)]
  rw [h]
  exact summable_jterm z

/-- The one-step ratio of the term sequence. -/
theorem jterm_succ (z : ℝ) (k : ℕ) :
    jterm z (k + 1) = jterm z k * ((z ^ 2 / 4) / ((k : ℝ) + 1) ^ 2) := by
  unfold jterm
  have h0 : (0 : ℝ) < (Nat.factorial k : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hf : ((Nat.factorial (k + 1) : ℕ) : ℝ) = ((k : ℝ) + 1) * (Nat.factorial k : ℝ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  rw [hf, pow_succ]
  field_simp

/-- **The terms are antitone from `k = 2` on, for `z ≤ 6`.**  This is the exact hypothesis
Mathlib's alternating-series bounds need, and the reason the first two terms are peeled off. -/
theorem jterm_antitone_shift {z : ℝ} (hz0 : 0 ≤ z) (hz6 : z ≤ 6) :
    Antitone (fun j : ℕ => jterm z (j + 2)) := by
  refine antitone_nat_of_succ_le (fun j => ?_)
  have hidx : j + 1 + 2 = j + 2 + 1 := by omega
  have hstep := jterm_succ z (j + 2)
  push_cast at hstep
  have hden : (0 : ℝ) < ((j : ℝ) + 2 + 1) ^ 2 := by positivity
  have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  have hz2 : z ^ 2 ≤ 36 := by nlinarith
  have hle : (z ^ 2 / 4) / ((j : ℝ) + 2 + 1) ^ 2 ≤ 1 := by
    rw [div_le_one hden]
    nlinarith [sq_nonneg ((j : ℝ))]
  have hnn : 0 ≤ jterm z (j + 2) := jterm_nonneg z _
  simp only [hidx, hstep]
  exact mul_le_of_le_one_right hnn hle

/-- The tail sum, with the shift's sign absorbed: `(-1)^(j+2) = (-1)^j`. -/
theorem J0_eq_head_add_tail (z : ℝ) :
    J0 z = (∑ k ∈ range 2, (-1 : ℝ) ^ k * jterm z k)
      + ∑' j, (-1 : ℝ) ^ j * jterm z (j + 2) := by
  have h := (summable_jterm_alt z).sum_add_tsum_nat_add 2
  have hsign : (fun j : ℕ => (-1 : ℝ) ^ (j + 2) * jterm z (j + 2))
      = fun j : ℕ => (-1 : ℝ) ^ j * jterm z (j + 2) := by
    funext j
    rw [pow_add]
    norm_num
  rw [J0, ← h, hsign]

theorem summable_tail (z : ℝ) : Summable (fun j : ℕ => (-1 : ℝ) ^ j * jterm z (j + 2)) := by
  have h := (summable_jterm_alt z).comp_injective (add_left_injective 2)
  have hsign : ((fun k => (-1 : ℝ) ^ k * jterm z k) ∘ fun j : ℕ => j + 2)
      = fun j : ℕ => (-1 : ℝ) ^ j * jterm z (j + 2) := by
    funext j
    simp only [Function.comp_apply]
    rw [pow_add]
    norm_num
  rwa [hsign] at h

/-- **The bracket.**  For `0 ≤ z ≤ 6`, `J₀` lies between two consecutive partial sums. -/
theorem besselP_le_J0_le_besselP {z : ℝ} (hz0 : 0 ≤ z) (hz6 : z ≤ 6) :
    besselP 13 z ≤ J0 z ∧ J0 z ≤ besselP 12 z := by
  set g : ℕ → ℝ := fun j => jterm z (j + 2) with hg
  have hanti : Antitone g := jterm_antitone_shift hz0 hz6
  have hsum : Summable (fun j : ℕ => (-1 : ℝ) ^ j * g j) := summable_tail z
  have htend : Tendsto (fun n => ∑ j ∈ range n, (-1 : ℝ) ^ j * g j) atTop
      (𝓝 (∑' j, (-1 : ℝ) ^ j * g j)) := hsum.hasSum.tendsto_sum_nat
  have hlow := hanti.alternating_series_le_tendsto htend 6
  have hhigh := hanti.tendsto_le_alternating_series htend 5
  have hhead := J0_eq_head_add_tail z
  have e13 : besselP 13 z
      = (∑ k ∈ range 2, (-1 : ℝ) ^ k * jterm z k) + ∑ j ∈ range (2 * 6), (-1 : ℝ) ^ j * g j := by
    simp only [besselP, hg, Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
    ring
  have e12 : besselP 12 z
      = (∑ k ∈ range 2, (-1 : ℝ) ^ k * jterm z k)
        + ∑ j ∈ range (2 * 5 + 1), (-1 : ℝ) ^ j * g j := by
    simp only [besselP, hg, Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
    ring
  constructor
  · rw [e13, hhead]
    linarith
  · rw [e12, hhead]
    linarith

/-! ### Continuity on `[0,6]`

`continuousOn_tsum` needs a `z`-free majorant, and `jterm 6` is one: the terms are monotone in
`z^2/4`, so the endpoint of the interval supplies the bound and its summability is already proved.
No new comparison series is needed. -/

theorem jterm_le_jterm_six {z : ℝ} (hz0 : 0 ≤ z) (hz6 : z ≤ 6) (k : ℕ) :
    jterm z k ≤ jterm 6 k := by
  unfold jterm
  have h2 : (0 : ℝ) ≤ z ^ 2 / 4 := by positivity
  have h1 : z ^ 2 / 4 ≤ (6 : ℝ) ^ 2 / 4 := by nlinarith
  have hpos : (0 : ℝ) < (Nat.factorial k : ℝ) := by exact_mod_cast Nat.factorial_pos k
  gcongr

theorem norm_jterm_alt_le {z : ℝ} (hz0 : 0 ≤ z) (hz6 : z ≤ 6) (k : ℕ) :
    ‖(-1 : ℝ) ^ k * jterm z k‖ ≤ jterm 6 k := by
  rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Real.norm_eq_abs,
    abs_of_nonneg (jterm_nonneg z k)]
  exact jterm_le_jterm_six hz0 hz6 k

theorem continuousOn_J0 : ContinuousOn J0 (Set.Icc (0 : ℝ) 6) := by
  have hterm : ∀ k : ℕ,
      ContinuousOn (fun z : ℝ => (-1 : ℝ) ^ k * jterm z k) (Set.Icc (0 : ℝ) 6) := by
    intro k
    unfold jterm
    fun_prop
  exact continuousOn_tsum hterm (summable_jterm 6) fun k _ hz => norm_jterm_alt_le hz.1 hz.2 k

/-! ### Strict decrease on `(0, 5/2]`, with no derivative at all

To know that the zero it has enclosed is the FIRST one, a certificate needs `J₀` to be injective
near it.  The write-up gets that from `J₀' = -J₁` together with the `J₁` series — an extra series
and a term-by-term differentiation.  Neither is needed.

**The DIFFERENCE of two values of `J₀` is itself an alternating series.**  With
`d k = jterm z' k - jterm z k >= 0` for `z <= z'`,

    J0 z - J0 z' = d 1 - d 2 + d 3 - ...

because `d 0 = 0`, and the same head-peeling bound used for the bracket gives
`J0 z - J0 z' >= d 1 - d 2`, which is positive as soon as `z^2/4 + z'^2/4 < 4`.  So the machinery
already in this file settles monotonicity, and the range it gives, `z' <= 5/2`, is the same range
the write-up's `J₁` argument covers.
-/

theorem jterm_mono_arg {z z' : ℝ} (hz0 : 0 ≤ z) (hzz : z ≤ z') (k : ℕ) :
    jterm z k ≤ jterm z' k := by
  unfold jterm
  have h2 : (0 : ℝ) ≤ z ^ 2 / 4 := by positivity
  have h1 : z ^ 2 / 4 ≤ z' ^ 2 / 4 := by nlinarith
  have hpos : (0 : ℝ) < (Nat.factorial k : ℝ) := by exact_mod_cast Nat.factorial_pos k
  gcongr

/-- `a^m * (b-a) ≤ b^(m+1) - a^(m+1)`, from the identity
`b^(m+1) - a^(m+1) = b*(b^m - a^m) + a^m*(b-a)`. -/
theorem pow_sub_ge {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (m : ℕ) :
    a ^ m * (b - a) ≤ b ^ (m + 1) - a ^ (m + 1) := by
  have hid : b ^ (m + 1) - a ^ (m + 1) = b * (b ^ m - a ^ m) + a ^ m * (b - a) := by ring
  rw [hid]
  have h1 : 0 ≤ b := le_trans ha hab
  have h2 : a ^ m ≤ b ^ m := pow_le_pow_left₀ ha hab m
  nlinarith [pow_nonneg ha m, pow_nonneg h1 m]

/-- The step inequality behind antitonicity of the difference terms. -/
theorem diff_step {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 25 / 16) (j : ℕ) :
    b ^ (j + 2) - a ^ (j + 2) ≤ ((j : ℝ) + 2) ^ 2 * (b ^ (j + 1) - a ^ (j + 1)) := by
  have h1 : 0 ≤ b := le_trans ha hab
  have hge : a ^ j * (b - a) ≤ b ^ (j + 1) - a ^ (j + 1) := pow_sub_ge ha hab j
  have hnn : 0 ≤ b ^ (j + 1) - a ^ (j + 1) := by
    have := pow_le_pow_left₀ ha hab (j + 1); linarith
  have hid : b ^ (j + 2) - a ^ (j + 2)
      = b * (b ^ (j + 1) - a ^ (j + 1)) + a ^ (j + 1) * (b - a) := by ring
  have hsmall : a ^ (j + 1) * (b - a) ≤ a * (b ^ (j + 1) - a ^ (j + 1)) := by
    have hrw : a ^ (j + 1) * (b - a) = a * (a ^ j * (b - a)) := by ring
    rw [hrw]
    exact mul_le_mul_of_nonneg_left hge ha
  have hfour : (4 : ℝ) ≤ ((j : ℝ) + 2) ^ 2 := by
    have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    nlinarith
  nlinarith [hnn, hsmall, hid, hfour]

/-- The difference terms are antitone from index `1` on. -/
theorem jterm_diff_antitone {z z' : ℝ} (hz0 : 0 ≤ z) (hzz : z ≤ z') (hz' : z' ≤ 5 / 2) :
    Antitone (fun j : ℕ => jterm z' (j + 1) - jterm z (j + 1)) := by
  refine antitone_nat_of_succ_le (fun j => ?_)
  have hidx : j + 1 + 1 = j + 2 := by omega
  simp only [hidx, jterm]
  have hpos1 : (0 : ℝ) < (Nat.factorial (j + 1) : ℝ) := by
    exact_mod_cast Nat.factorial_pos (j + 1)
  have hpos2 : (0 : ℝ) < (Nat.factorial (j + 2) : ℝ) := by
    exact_mod_cast Nat.factorial_pos (j + 2)
  rw [div_sub_div_same, div_sub_div_same, div_le_div_iff₀ (by positivity) (by positivity)]
  have hfac : (Nat.factorial (j + 2) : ℝ) = ((j : ℝ) + 2) * (Nat.factorial (j + 1) : ℝ) := by
    rw [show j + 2 = (j + 1) + 1 from rfl, Nat.factorial_succ]
    push_cast
    ring
  rw [hfac]
  have hstep := diff_step (a := z ^ 2 / 4) (b := z' ^ 2 / 4) (by positivity) (by nlinarith)
    (by nlinarith) j
  have hmul := mul_le_mul_of_nonneg_right hstep
    (sq_nonneg ((Nat.factorial (j + 1) : ℝ)))
  nlinarith [hmul]

theorem summable_jterm_shift (z : ℝ) : Summable (fun j : ℕ => jterm z (j + 1)) :=
  (summable_nat_add_iff 1).2 (summable_jterm z)

theorem summable_jterm_diff (z z' : ℝ) :
    Summable (fun j : ℕ => (-1 : ℝ) ^ j * (jterm z' (j + 1) - jterm z (j + 1))) := by
  refine Summable.of_norm ?_
  have hb : ∀ j : ℕ, ‖(-1 : ℝ) ^ j * (jterm z' (j + 1) - jterm z (j + 1))‖
      ≤ jterm z' (j + 1) + jterm z (j + 1) := by
    intro j
    rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Real.norm_eq_abs]
    have h1 : 0 ≤ jterm z' (j + 1) := jterm_nonneg z' _
    have h2 : 0 ≤ jterm z (j + 1) := jterm_nonneg z _
    rw [abs_le]
    constructor <;> linarith [abs_nonneg (jterm z' (j + 1) - jterm z (j + 1))]
  exact Summable.of_nonneg_of_le (fun j => norm_nonneg _) hb
    ((summable_jterm_shift z').add (summable_jterm_shift z))

/-- `J₀ z - J₀ z'` as the alternating series in the term differences.  The head vanishes because
`jterm _ 0 = 1` for every argument. -/
theorem J0_sub_eq (z z' : ℝ) :
    J0 z - J0 z' = ∑' j : ℕ, (-1 : ℝ) ^ j * (jterm z' (j + 1) - jterm z (j + 1)) := by
  have hs := summable_jterm_alt z
  have hs' := summable_jterm_alt z'
  have hd : Summable (fun k => (-1 : ℝ) ^ k * jterm z k - (-1 : ℝ) ^ k * jterm z' k) := hs.sub hs'
  have hsplit := hd.sum_add_tsum_nat_add 1
  have hzero : ∑ i ∈ Finset.range 1,
      ((-1 : ℝ) ^ i * jterm z i - (-1 : ℝ) ^ i * jterm z' i) = 0 := by
    simp [jterm]
  have hterm : (fun j : ℕ => (-1 : ℝ) ^ (j + 1) * jterm z (j + 1)
      - (-1 : ℝ) ^ (j + 1) * jterm z' (j + 1))
      = fun j : ℕ => (-1 : ℝ) ^ j * (jterm z' (j + 1) - jterm z (j + 1)) := by
    funext j
    rw [pow_succ]
    ring
  rw [J0, J0, ← hs.tsum_sub hs', ← hsplit, hzero, hterm, zero_add]

/-- **`J₀` is strictly decreasing on `(0, 5/2]`.** -/
theorem J0_lt_J0_of_lt {z z' : ℝ} (hz0 : 0 < z) (hzz : z < z') (hz' : z' ≤ 5 / 2) :
    J0 z' < J0 z := by
  have hz0' : (0 : ℝ) ≤ z := hz0.le
  have hanti : Antitone (fun j : ℕ => jterm z' (j + 1) - jterm z (j + 1)) :=
    jterm_diff_antitone hz0' hzz.le hz'
  have hsum := summable_jterm_diff z z'
  have htend : Tendsto (fun n => ∑ j ∈ Finset.range n,
      (-1 : ℝ) ^ j * (jterm z' (j + 1) - jterm z (j + 1))) atTop
      (𝓝 (∑' j, (-1 : ℝ) ^ j * (jterm z' (j + 1) - jterm z (j + 1)))) :=
    hsum.hasSum.tendsto_sum_nat
  have hlow := hanti.alternating_series_le_tendsto htend 1
  have hexp : ∑ j ∈ Finset.range (2 * 1), (-1 : ℝ) ^ j * (jterm z' (j + 1) - jterm z (j + 1))
      = (jterm z' 1 - jterm z 1) - (jterm z' 2 - jterm z 2) := by
    norm_num [Finset.sum_range_succ]
    ring
  have hd1 : jterm z' 1 - jterm z 1 = z' ^ 2 / 4 - z ^ 2 / 4 := by simp [jterm]
  have hd2 : jterm z' 2 - jterm z 2 = ((z' ^ 2 / 4) ^ 2 - (z ^ 2 / 4) ^ 2) / 4 := by
    simp [jterm, Nat.factorial]
    ring
  have hgap : 0 < (jterm z' 1 - jterm z 1) - (jterm z' 2 - jterm z 2) := by
    rw [hd1, hd2]
    have h1 : z ^ 2 < z' ^ 2 := by nlinarith
    have h2 : z' ^ 2 ≤ 25 / 4 := by nlinarith
    nlinarith
  have hkey := J0_sub_eq z z'
  rw [hexp] at hlow
  linarith [hgap, hkey, hlow]

end Principia.Common
