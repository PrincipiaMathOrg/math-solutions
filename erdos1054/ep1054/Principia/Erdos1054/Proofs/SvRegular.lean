/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Erdos1054.Spine
import Principia.Erdos1054.Basic
import Principia.Erdos1054.Density
import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.Chebyshev

set_option autoImplicit false

/-!
# EP1054 §4.3: arithmetic regularity and smooth-part classes (the `SvRegular` package)

Source: `Campaigns/Erdos-1054/collab-paper/EP1054.tex`, lines 1304–1558 (the subsection
"Arithmetic regularity and smooth-part classes" and the two reciprocal estimates that open the
proof of `prop:sv-second-moment`), and lines 1863–1869 (the per-class image bound).

## Obligations discharged

Leaves (proved from the definitions and pinned Mathlib alone):
* `leaf_Eq_SvHarmonicDensityZero` — `eq:sv-harmonic-density-zero` (lines 1443–1448): exact Abel
  summation `∑_{n ≤ N, n ∈ E} 1/n = A(N)/(N+1) + ∑_{m ≤ N} A(m)/(m(m+1))`
  (`sum_inv_filter_eq`), then `A(m) ≤ εm` for large `m` and `H_N ≤ 1 + log N`.

Links (proved from exactly the dependencies the spine names):
* `link_Eq_SmoothPartPeriodCount` (lines 1362–1369), from `Notation_Delta_density`, with `C = 1`:
  `D_y(n) = d ⟺ n = du` with `u` `y`-rough (`smoothPart_eq_iff`), so the count is the count of
  integers `≤ T/d` coprime to `y#` (`cnt_smoothPart_eq`), a `y#`-periodic set whose density is
  `Δ(y)` (`Notation_Delta_density` and `HasDens.unique`); complete periods give the error `≤ y#`.
* `link_Lem_SmoothPartInput` (lines 1348–1389), from `Eq_SmoothPartPeriodCount`, `Std_Mertens1`,
  `Std_Mertens3`: the two-sided bound uses `y# ≤ 4^y` and `Y = o(log X)` (`eventually_err_small`);
  the tail uses Legendre (`sum_log_smoothPart_le`: `∏_{n≤N} D_Y(n)` is a `Y`-smooth divisor of `N!`)
  and Markov (`cnt_smoothPart_large_le`).
* `link_Lem_SvClasses` (lines 1486–1527), from `Lem_SmoothPartInput` (at `Y = SV.Ycut`, which tends
  to infinity and is `o(log X)`: `tendsto_Ycut`, `Ycut_littleO`) and `Std_Mertens3`; the Euler
  product bound `∑_{P^+(d) ≤ Y} 1/d ≤ Δ(Y)^{-1}` is `sum_inv_smooth_le`; disjointness of the images
  is property (i) at `t = M` of the `SV.RegularFamily` hypothesis.
* `link_Eq_SvKReciprocal` (lines 1545–1552), from `Eq_SmoothPartPeriodCount` and `Std_Mertens3`,
  with the absolute constant `e^{-γ} + 2`: Abel summation over `SV.kSet` (`sum_inv_finset_eq`) and
  the period count at every scale `T ≤ X^{1/60}` with the level fixed.
* `link_Eq_SvMReciprocal` (lines 1553–1558), from `Eq_SvKReciprocal` and `Std_Mertens2`
  (`primesIoc_recip_le`: `∑_{X^{θ₁} < p ≤ X^{θ₂}} 1/p ≤ θ₂/θ₁` for large `X`).
* `link_Claim_SvClassImage` (lines 1863–1869), from `Claim_SvCauchySchwarz` and
  `Prop_SvSecondMoment`, with `c' = c₁²/max(C, 1)`.
* `link_Lem_SvRegular` (lines 1394–1480), from `Lem_SvA0` (the count, `eq:sv-two-sided` and
  `q > n^{7/9}`; the uniqueness part is not needed), `Lem_LPInputs`, `Eq_SvHarmonicDensityZero`,
  `Cite_Pollack_Thm14` and `Std_Mertens2`. The family is `famA D E`: the members of `𝒜₀(X)` all of
  whose tuples avoid one density-zero set `E ⊇ E_{LP2.1} ∪ E_{LP2.2} ∪ E_{LP2.5} ∪ E_{Pollack}` at
  the four levels `k, rk, qrk, pqrk`, and whose `k` has no prime factor in `(Y, y(X)]`
  (`GoodT`). The count `#𝒜(X) ≥ c₀X/2` (`famA_count`) bounds each kind of deleted member by
  Chebyshev's `π(x) ≤ 8x/log x` for the prime `p` (`card_primesLE_le`, `card_Sset_le`), the
  injectivity of `(q, r, k) ↦ rk, qrk` on the ranges (`rk_inj`, `qrk_inj`), the harmonic
  density-zero estimate at the scales `X^{1/60}, X^{1/10}, X^{7/15}`, Mertens' second theorem over
  the power intervals (`primesIoc_recip_le`) and over `(Y, y(X)]` (`mid_small`, which uses
  `y(X)/Y ≤ log log X/(log log X − log 120)`). The listed properties (`famA_regular`) follow from
  the Luca–Pomerance conclusions at each level (`regularAt_of`, `level_regular`), the monotonicity
  of `y` on `[e^{e^e}, ∞)` (`yOf_mono`), and `p, q, r > X^{1/15} > y(X)`.

Nothing is assumed beyond the hypotheses of each link: every theorem's axioms are
`[propext, Classical.choice, Quot.sound]`.
-/

namespace Principia.Erdos1054.Proofs.SvRegular

open Finset Filter Principia.Erdos1054

/-! ## Smooth and rough integers -/

theorem isSmooth_one (y : ℝ) : IsSmooth y 1 := by
  intro p hp
  simp at hp

theorem isSmooth_of_dvd {y : ℝ} {e m : ℕ} (hm : m ≠ 0) (he : e ∣ m) (h : IsSmooth y m) :
    IsSmooth y e := fun p hp => h p (Nat.primeFactors_mono he hm hp)

theorem isSmooth_mul {y : ℝ} {a b : ℕ} (ha : IsSmooth y a) (hb : IsSmooth y b) :
    IsSmooth y (a * b) := by
  intro p hp
  have hp' := Nat.mem_primeFactors.1 hp
  rcases (Nat.Prime.dvd_mul hp'.1).1 hp'.2.1 with h | h
  · exact ha p (Nat.mem_primeFactors.2 ⟨hp'.1, h, fun h0 => by simp [h0] at hp'⟩)
  · exact hb p (Nat.mem_primeFactors.2 ⟨hp'.1, h, fun h0 => by simp [h0] at hp'⟩)

theorem isSmooth_lcm {y : ℝ} {a b : ℕ} (ha : IsSmooth y a) (hb : IsSmooth y b) :
    IsSmooth y (Nat.lcm a b) := by
  intro p hp
  have hp' := Nat.mem_primeFactors.1 hp
  have hab : a ≠ 0 ∧ b ≠ 0 := by
    constructor
    · rintro rfl; simp at hp'
    · rintro rfl; simp at hp'
  have hd : p ∣ a * b := hp'.2.1.trans (Nat.lcm_dvd_mul a b)
  rcases (Nat.Prime.dvd_mul hp'.1).1 hd with h | h
  · exact ha p (Nat.mem_primeFactors.2 ⟨hp'.1, h, hab.1⟩)
  · exact hb p (Nat.mem_primeFactors.2 ⟨hp'.1, h, hab.2⟩)

theorem isRough_of_dvd {y : ℝ} {e m : ℕ} (hm : m ≠ 0) (he : e ∣ m) (h : IsRough y m) :
    IsRough y e := fun p hp => h p (Nat.primeFactors_mono he hm hp)

/-- A prime divides `y#` iff it is at most `y`. -/
theorem prime_dvd_primorialR_iff {y : ℝ} {p : ℕ} (hp : p.Prime) :
    p ∣ primorialR y ↔ (p : ℝ) ≤ y := by
  unfold primorialR
  rw [hp.dvd_primorial_iff]
  constructor
  · intro h
    have h1 : 1 ≤ ⌊y⌋₊ := le_trans hp.one_lt.le h
    have hy : 0 ≤ y := by
      by_contra hy
      push Not at hy
      rw [Nat.floor_eq_zero.2 (by linarith)] at h1
      omega
    exact (Nat.cast_le.2 h).trans (Nat.floor_le hy)
  · intro h
    exact Nat.le_floor h

theorem isRough_iff_coprime {y : ℝ} {u : ℕ} (hu : u ≠ 0) :
    IsRough y u ↔ Nat.Coprime u (primorialR y) := by
  constructor
  · intro h
    refine Nat.coprime_of_dvd fun k hk hku hkP => ?_
    have h1 := h k (Nat.mem_primeFactors.2 ⟨hk, hku, hu⟩)
    have h2 := (prime_dvd_primorialR_iff hk).1 hkP
    linarith
  · intro h p hp
    have hp' := Nat.mem_primeFactors.1 hp
    by_contra hle
    push Not at hle
    have hdP := (prime_dvd_primorialR_iff hp'.1).2 hle
    have := Nat.dvd_one.1 ((Nat.dvd_gcd hp'.2.1 hdP).trans (by rw [h]))
    exact hp'.1.one_lt.ne' this

theorem coprime_of_smooth_rough {y : ℝ} {a b : ℕ} (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (ha : IsSmooth y a) (hb : IsRough y b) : Nat.Coprime a b := by
  refine Nat.coprime_of_dvd fun k hk hka hkb => ?_
  have h1 := ha k (Nat.mem_primeFactors.2 ⟨hk, hka, ha0⟩)
  have h2 := hb k (Nat.mem_primeFactors.2 ⟨hk, hkb, hb0⟩)
  linarith

/-! ## The largest `y`-smooth divisor -/

open Classical in
theorem smoothPart_eq_sup (y : ℝ) (n : ℕ) :
    SV.smoothPart y n = (n.divisors.filter (fun d => IsSmooth y d)).sup id := rfl

theorem smoothPart_spec {y : ℝ} {n : ℕ} (hn : n ≠ 0) :
    SV.smoothPart y n ∣ n ∧ IsSmooth y (SV.smoothPart y n) := by
  classical
  rw [smoothPart_eq_sup]
  have hne : (n.divisors.filter (fun d => IsSmooth y d)).Nonempty :=
    ⟨1, Finset.mem_filter.2 ⟨Nat.one_mem_divisors.2 hn, isSmooth_one y⟩⟩
  obtain ⟨i, hi, heq⟩ := Finset.exists_mem_eq_sup _ hne id
  rw [heq]
  rw [Finset.mem_filter, Nat.mem_divisors] at hi
  exact ⟨hi.1.1, hi.2⟩

theorem le_smoothPart {y : ℝ} {n e : ℕ} (hn : n ≠ 0) (he : e ∣ n) (hs : IsSmooth y e) :
    e ≤ SV.smoothPart y n := by
  classical
  rw [smoothPart_eq_sup]
  exact Finset.le_sup (f := id) (Finset.mem_filter.2 ⟨Nat.mem_divisors.2 ⟨he, hn⟩, hs⟩)

theorem smoothPart_ne_zero {y : ℝ} {n : ℕ} (hn : n ≠ 0) : SV.smoothPart y n ≠ 0 := by
  have := le_smoothPart hn (one_dvd n) (isSmooth_one y)
  omega

theorem dvd_smoothPart {y : ℝ} {n e : ℕ} (hn : n ≠ 0) (he : e ∣ n) (hs : IsSmooth y e) :
    e ∣ SV.smoothPart y n := by
  obtain ⟨hmn, hms⟩ := smoothPart_spec (y := y) hn
  set m := SV.smoothPart y n with hm
  have hm0 : m ≠ 0 := smoothPart_ne_zero hn
  have hl : Nat.lcm e m ∣ n := Nat.lcm_dvd he hmn
  have hl2 : Nat.lcm e m ≤ m := le_smoothPart hn hl (isSmooth_lcm hs hms)
  have hl3 : m ∣ Nat.lcm e m := Nat.dvd_lcm_right e m
  have hl0 : Nat.lcm e m ≠ 0 := Nat.lcm_ne_zero (ne_zero_of_dvd_ne_zero hn he) hm0
  have heq : Nat.lcm e m = m := le_antisymm hl2 (Nat.le_of_dvd (Nat.pos_of_ne_zero hl0) hl3)
  rw [← heq]
  exact Nat.dvd_lcm_left e m

/-- `D_y(d w) = d` for `y`-smooth `d` and `y`-rough `w`. -/
theorem smoothPart_mul_rough {y : ℝ} {d w : ℕ} (hd0 : d ≠ 0) (hw0 : w ≠ 0)
    (hd : IsSmooth y d) (hw : IsRough y w) : SV.smoothPart y (d * w) = d := by
  have hn : d * w ≠ 0 := mul_ne_zero hd0 hw0
  obtain ⟨hmn, hms⟩ := smoothPart_spec (y := y) hn
  have h1 : d ∣ SV.smoothPart y (d * w) := dvd_smoothPart hn (dvd_mul_right d w) hd
  have hcop : Nat.Coprime (SV.smoothPart y (d * w)) w :=
    coprime_of_smooth_rough (smoothPart_ne_zero hn) hw0 hms hw
  have h2 : SV.smoothPart y (d * w) ∣ d := hcop.dvd_of_dvd_mul_right hmn
  exact Nat.dvd_antisymm h2 h1

/-- If `D_y(n) = d` then `n / d` is `y`-rough. -/
theorem isRough_div_smoothPart {y : ℝ} {n : ℕ} (hn : n ≠ 0) :
    IsRough y (n / SV.smoothPart y n) := by
  obtain ⟨hmn, hms⟩ := smoothPart_spec (y := y) hn
  set m := SV.smoothPart y n with hm
  have hm0 : m ≠ 0 := smoothPart_ne_zero hn
  intro p hp
  have hp' := Nat.mem_primeFactors.1 hp
  by_contra hle
  push Not at hle
  have hps : IsSmooth y p := by
    intro q hq
    rw [Nat.Prime.primeFactors hp'.1, Finset.mem_singleton] at hq
    rw [hq]
    exact hle
  have hdiv : m * p ∣ n := by
    obtain ⟨u, hu⟩ := hmn
    have hu' : n / m = u := by rw [hu, Nat.mul_div_cancel_left u (Nat.pos_of_ne_zero hm0)]
    rw [hu'] at hp'
    obtain ⟨v, hv⟩ := hp'.2.1
    exact ⟨v, by rw [hu, hv]; ring⟩
  have h1 := dvd_smoothPart hn hdiv (isSmooth_mul hms hps)
  rw [← hm] at h1
  have h2 : m * p ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) h1
  have h3 : m * 2 ≤ m * p := Nat.mul_le_mul_left m hp'.1.two_le
  omega

/-- For `y`-smooth `d ≥ 1` and `n ≥ 1`: `D_y(n) = d ↔ n = d u` with `u` `y`-rough. -/
theorem smoothPart_eq_iff {y : ℝ} {n d : ℕ} (hn : n ≠ 0) (hd0 : d ≠ 0) (hd : IsSmooth y d) :
    SV.smoothPart y n = d ↔ ∃ u, n = d * u ∧ IsRough y u := by
  constructor
  · intro h
    obtain ⟨hmn, _⟩ := smoothPart_spec (y := y) hn
    rw [h] at hmn
    refine ⟨n / d, (Nat.mul_div_cancel' hmn).symm, ?_⟩
    have := isRough_div_smoothPart (y := y) hn
    rwa [h] at this
  · rintro ⟨u, rfl, hu⟩
    have hu0 : u ≠ 0 := by rintro rfl; simp at hn
    exact smoothPart_mul_rough hd0 hu0 hd hu

/-! ## Counting a smooth-part class: complete periods -/

theorem cnt_smoothPart_eq {y T : ℝ} {d : ℕ} (hd0 : d ≠ 0) (hd : IsSmooth y d) :
    cnt {n : ℕ | SV.smoothPart y n = d} T =
      cnt {u : ℕ | Nat.Coprime u (primorialR y)} (T / d) := by
  have hdp : 0 < d := Nat.pos_of_ne_zero hd0
  unfold cnt
  rw [Nat.floor_div_natCast]
  symm
  refine Finset.card_nbij (fun u => d * u) ?_ ?_ ?_
  · intro u hu
    rw [Finset.mem_coe, mem_cntFinset] at hu
    rw [Finset.mem_coe, mem_cntFinset]
    have hu0 : u ≠ 0 := by omega
    have h2 := (Nat.le_div_iff_mul_le hdp).1 hu.1.2
    refine ⟨⟨Nat.mul_pos hdp hu.1.1, show d * u ≤ _ by rw [mul_comm]; exact h2⟩, ?_⟩
    show SV.smoothPart y (d * u) = d
    exact smoothPart_mul_rough hd0 hu0 hd ((isRough_iff_coprime hu0).2 hu.2)
  · intro a _ b _ h
    exact Nat.eq_of_mul_eq_mul_left hdp h
  · intro n hn
    rw [Finset.mem_coe, mem_cntFinset] at hn
    have hn0 : n ≠ 0 := by omega
    have h3 : SV.smoothPart y n = d := hn.2
    obtain ⟨u, rfl, hu⟩ := (smoothPart_eq_iff hn0 hd0 hd).1 h3
    have hu0 : u ≠ 0 := by rintro rfl; simp at hn0
    refine ⟨u, ?_, rfl⟩
    rw [Finset.mem_coe, mem_cntFinset]
    refine ⟨⟨Nat.pos_of_ne_zero hu0, ?_⟩, (isRough_iff_coprime hu0).1 hu⟩
    rw [Nat.le_div_iff_mul_le hdp, mul_comm]
    exact hn.1.2

theorem cnt_coprime_primorial_div (y : ℝ)
    (hNot : Principia.Erdos1054.Notation_Delta_density) :
    (cnt {u : ℕ | Nat.Coprime u (primorialR y)} (primorialR y : ℝ) : ℝ) / (primorialR y : ℝ) =
      Delta y := by
  have hPpos : 0 < primorialR y := primorial_pos _
  have hper : ∀ N, N + primorialR y ∈ {u : ℕ | Nat.Coprime u (primorialR y)} ↔
      N ∈ {u : ℕ | Nat.Coprime u (primorialR y)} := fun N => Nat.coprime_add_self_left
  by_cases hy : 1 ≤ y
  · exact HasDens.unique (hasDens_of_periodic hPpos hper) (hNot y hy).2
  · push Not at hy
    have hfl : ⌊y⌋₊ = 0 := Nat.floor_eq_zero.2 hy
    have hP1 : primorialR y = 1 := by unfold primorialR; rw [hfl]; rfl
    have hD : Delta y = 1 := by
      unfold Delta
      rw [hfl, zero_add, Finset.range_one, Finset.filter_singleton, if_neg Nat.not_prime_zero,
        Finset.prod_empty]
    rw [hD, hP1]
    have hc : cnt {u : ℕ | Nat.Coprime u 1} ((1 : ℕ) : ℝ) = 1 := by
      refine le_antisymm (cnt_natCast_le _ _) ?_
      unfold cnt
      rw [Nat.floor_natCast]
      exact Finset.card_pos.2 ⟨1, mem_cntFinset.2 ⟨⟨le_rfl, le_rfl⟩, Nat.coprime_one_right 1⟩⟩
    rw [hc]
    norm_num

end Principia.Erdos1054.Proofs.SvRegular

namespace Principia.Erdos1054.Proofs

open Finset Filter Principia.Erdos1054 Principia.Erdos1054.Proofs.SvRegular

/-- **`Eq_SmoothPartPeriodCount`** (EP1054.tex lines 1362–1369), with `C = 1`. -/
theorem link_Eq_SmoothPartPeriodCount :
    Principia.Erdos1054.Spine.Link_Eq_SmoothPartPeriodCount := by
  intro hNot
  refine ⟨1, fun y T d hT hd1 hd => ?_⟩
  have hd0 : d ≠ 0 := by omega
  have hPpos : 0 < primorialR y := primorial_pos _
  have hper : ∀ N, N + primorialR y ∈ {u : ℕ | Nat.Coprime u (primorialR y)} ↔
      N ∈ {u : ℕ | Nat.Coprime u (primorialR y)} := fun N => Nat.coprime_add_self_left
  have hdR : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd0
  have h1 := abs_cnt_sub_le_period hPpos hper (div_nonneg hT hdR.le)
  have hkey := cnt_coprime_primorial_div y hNot
  rw [cnt_smoothPart_eq hd0 hd, one_mul]
  rw [mul_div_right_comm, hkey, mul_comm] at h1
  exact h1

end Principia.Erdos1054.Proofs

namespace Principia.Erdos1054.Proofs.SvRegular

open Finset Filter Principia.Erdos1054

/-! ## Partial summation for reciprocal sums over a set -/

theorem sum_Icc_inv_le_one_add_log (n : ℕ) :
    ∑ i ∈ Finset.Icc 1 n, (1 : ℝ) / i ≤ 1 + Real.log n := by
  have h := harmonic_le_one_add_log n
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at h
  simpa [one_div] using h

open Classical in
/-- Abel summation, exact form: `∑_{n ≤ N, n ∈ S} 1/n = A(N)/(N+1) + ∑_{m ≤ N} A(m)/(m(m+1))`. -/
theorem sum_inv_filter_eq (S : Set ℕ) (N : ℕ) :
    ∑ n ∈ (Finset.Icc 1 N).filter (· ∈ S), (1 : ℝ) / n =
      (cnt S (N : ℝ) : ℝ) / ((N : ℝ) + 1) +
        ∑ m ∈ Finset.Icc 1 N, (cnt S (m : ℝ) : ℝ) / ((m : ℝ) * ((m : ℝ) + 1)) := by
  induction N with
  | zero => simp [cnt_zero]
  | succ N ih =>
    rw [Finset.sum_filter, Finset.sum_Icc_succ_top (by omega), ← Finset.sum_filter, ih,
      Finset.sum_Icc_succ_top (by omega), cnt_succ]
    have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have hN2 : (0 : ℝ) < (N : ℝ) + 1 + 1 := by positivity
    split_ifs with h
    · push_cast
      field_simp
      ring
    · push_cast
      field_simp
      ring

end Principia.Erdos1054.Proofs.SvRegular

namespace Principia.Erdos1054.Proofs

open Finset Filter Principia.Erdos1054 Principia.Erdos1054.Proofs.SvRegular

/-- **`eq:sv-harmonic-density-zero`** (EP1054.tex lines 1443–1448). -/
theorem leaf_Eq_SvHarmonicDensityZero : Principia.Erdos1054.Eq_SvHarmonicDensityZero := by
  intro E hE ε hε
  obtain ⟨N₀, hN₀⟩ :=
    eventually_atTop.1 (densZero_iff_eventually_le.1 hE (ε / 4) (by positivity))
  set A : ℝ := (1 + (N₀ : ℝ) + ε) * 2 / ε with hA
  refine ⟨Real.exp A, fun T hT => ?_⟩
  have hT0 : 0 < T := lt_of_lt_of_le (Real.exp_pos A) hT
  have hlogT : A ≤ Real.log T := by
    rw [← Real.log_exp A]
    exact Real.log_le_log (Real.exp_pos A) hT
  have hεA : ε * A = (1 + (N₀ : ℝ) + ε) * 2 := by
    rw [hA]
    field_simp
  set N := ⌊T⌋₊ with hNdef
  rw [sum_inv_filter_eq E N]
  have hfirst : (cnt E (N : ℝ) : ℝ) / ((N : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]
    have : (cnt E (N : ℝ) : ℝ) ≤ N := by exact_mod_cast cnt_natCast_le E N
    linarith
  have hterm : ∀ m ∈ Finset.Icc 1 N, (cnt E (m : ℝ) : ℝ) / ((m : ℝ) * ((m : ℝ) + 1)) ≤
      (if m < N₀ then (1 : ℝ) else 0) + ε / 4 * (1 / (m : ℝ)) := by
    intro m hm
    have hm1 : 1 ≤ m := (Finset.mem_Icc.1 hm).1
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm1
    have hden : (0 : ℝ) < (m : ℝ) * ((m : ℝ) + 1) := by positivity
    have hcm : (cnt E (m : ℝ) : ℝ) ≤ m := by exact_mod_cast cnt_natCast_le E m
    split_ifs with hlt
    · have h1 : (cnt E (m : ℝ) : ℝ) / ((m : ℝ) * ((m : ℝ) + 1)) ≤ 1 := by
        rw [div_le_one hden]
        nlinarith
      have h2 : 0 ≤ ε / 4 * (1 / (m : ℝ)) := by positivity
      linarith
    · push Not at hlt
      have hc := hN₀ m hlt
      rw [zero_add, div_le_iff₀ hden]
      have he : ε / 4 * (1 / (m : ℝ)) * ((m : ℝ) * ((m : ℝ) + 1)) = ε / 4 * ((m : ℝ) + 1) := by
        field_simp
      rw [he]
      nlinarith
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib, Finset.sum_boole, ← Finset.mul_sum] at hsum
  have hcard : (((Finset.Icc 1 N).filter (fun m => m < N₀)).card : ℝ) ≤ N₀ := by
    have : ((Finset.Icc 1 N).filter (fun m => m < N₀)).card ≤ N₀ := by
      calc _ ≤ (Finset.range N₀).card := Finset.card_le_card (fun m hm => by
              rw [Finset.mem_filter] at hm
              exact Finset.mem_range.2 hm.2)
        _ = N₀ := Finset.card_range N₀
    exact_mod_cast this
  have hH := sum_Icc_inv_le_one_add_log N
  have hlogN : Real.log N ≤ Real.log T := by
    rcases Nat.eq_zero_or_pos N with h0 | hpos
    · rw [h0, Nat.cast_zero, Real.log_zero]
      have : 0 < A := by positivity
      linarith
    · exact Real.log_le_log (by exact_mod_cast hpos) (Nat.floor_le hT0.le)
  have hε4 : 0 ≤ ε / 4 := by positivity
  have hH' := mul_le_mul_of_nonneg_left (hH.trans (by linarith : 1 + Real.log N ≤ 1 + Real.log T)) hε4
  have hεL : ε * A ≤ ε * Real.log T := mul_le_mul_of_nonneg_left hlogT hε.le
  nlinarith

end Principia.Erdos1054.Proofs

namespace Principia.Erdos1054.Proofs

open Finset Filter Principia.Erdos1054 Principia.Erdos1054.Proofs.SvRegular

/-- **`Claim_SvClassImage`** (EP1054.tex lines 1863–1869). -/
theorem link_Claim_SvClassImage : Principia.Erdos1054.Spine.Link_Claim_SvClassImage := by
  intro hCS hSM δ hδ hδ1 D hD 𝒜 h𝒜 c c₁ c₂ c₃ hc hc₁ hc₂ hc₃
  obtain ⟨C, X₀, hX₀⟩ := hSM δ hδ hδ1 D hD 𝒜 h𝒜 c c₁ c₂ c₃ hc hc₁ hc₂ hc₃
  have hm1 : (0 : ℝ) < max C 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨c₁ ^ 2 / max C 1, by positivity, X₀, fun X hX 𝒟 hcl d hd => ?_⟩
  have hsm := hX₀ X hX 𝒟 hcl d hd
  have hlow := (hcl.2.1.1 d hd).1
  set Q := X / ((d : ℝ) * Real.log (SV.Ycut X)) with hQdef
  set S := SV.classFin (𝒜 X) X d with hSdef
  have hcs := hCS S aliquot
  have himg0 : (0 : ℝ) ≤ ((S.image aliquot).card : ℝ) := Nat.cast_nonneg _
  by_cases hQ : Q ≤ 0
  · calc c₁ ^ 2 / max C 1 * Q ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (by positivity) hQ
      _ ≤ _ := himg0
  · push Not at hQ
    have h1 : (c₁ * Q) ^ 2 ≤ ((S.card : ℕ) : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hlow 2
    have h2 : ∑ u ∈ S.image aliquot, (((S.filter (fun M => aliquot M = u)).card : ℕ) : ℝ) ^ 2 ≤
        max C 1 * Q := hsm.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hQ.le)
    have h3 := hcs.trans (mul_le_mul_of_nonneg_left h2 himg0)
    rw [div_mul_eq_mul_div, div_le_iff₀ hm1]
    have h4 : Q * (c₁ ^ 2 * Q) ≤ Q * (((S.image aliquot).card : ℝ) * max C 1) := by nlinarith
    exact le_of_mul_le_mul_left h4 hQ

end Principia.Erdos1054.Proofs

namespace Principia.Erdos1054.Proofs.SvRegular

open Finset Filter Principia.Erdos1054

/-! ## Asymptotics of the level `Y = y(X^{1/120})` -/

theorem tendsto_div_log_atTop : Tendsto (fun L : ℝ => L / Real.log L) atTop atTop := by
  have hg : Tendsto (fun L : ℝ => L ^ ((1 : ℝ) / 2) / 2) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).atTop_div_const (by norm_num)
  refine tendsto_atTop_mono' atTop ?_ hg
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with L hL
  have hL0 : 0 < L := by linarith
  have hlog : 0 < Real.log L := Real.log_pos hL
  have hb := Real.log_le_rpow_div hL0.le (by norm_num : (0 : ℝ) < 1 / 2)
  rw [le_div_iff₀ hlog]
  have hsq : L ^ ((1 : ℝ) / 2) * L ^ ((1 : ℝ) / 2) = L := by
    rw [← Real.rpow_add hL0]
    norm_num
  have hpos : 0 ≤ L ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hL0.le _
  calc L ^ ((1 : ℝ) / 2) / 2 * Real.log L
      ≤ L ^ ((1 : ℝ) / 2) / 2 * (L ^ ((1 : ℝ) / 2) / (1 / 2)) := by gcongr
    _ = L ^ ((1 : ℝ) / 2) * L ^ ((1 : ℝ) / 2) := by ring
    _ = L := hsq

theorem Ycut_eq (X : ℝ) : SV.Ycut X = Real.log (Real.log (X ^ ((1 : ℝ) / 120))) /
    Real.log (Real.log (Real.log (X ^ ((1 : ℝ) / 120)))) := rfl

theorem tendsto_loglog_rpow : Tendsto (fun X : ℝ => Real.log (Real.log (X ^ ((1 : ℝ) / 120))))
    atTop atTop :=
  Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp (tendsto_rpow_atTop (by norm_num)))

theorem tendsto_Ycut : Tendsto SV.Ycut atTop atTop :=
  (tendsto_div_log_atTop.comp tendsto_loglog_rpow).congr (fun X => (Ycut_eq X).symm)

/-- For large `X`, `0 ≤ Y ≤ log log X`. -/
theorem eventually_Ycut_le_loglog :
    ∀ᶠ X : ℝ in atTop, 0 ≤ SV.Ycut X ∧ SV.Ycut X ≤ Real.log (Real.log X) := by
  have hu : Tendsto (fun X : ℝ => Real.log (X ^ ((1 : ℝ) / 120))) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_rpow_atTop (by norm_num))
  filter_upwards [tendsto_loglog_rpow.eventually_ge_atTop (Real.exp 1),
    hu.eventually_ge_atTop 1, eventually_gt_atTop (1 : ℝ)] with X hL hlu hX
  have hL0 : 0 < Real.log (Real.log (X ^ ((1 : ℝ) / 120))) :=
    lt_of_lt_of_le (Real.exp_pos 1) hL
  have hlogL : 1 ≤ Real.log (Real.log (Real.log (X ^ ((1 : ℝ) / 120)))) := by
    have := Real.log_le_log (Real.exp_pos 1) hL
    rwa [Real.log_exp] at this
  rw [Ycut_eq]
  refine ⟨div_nonneg hL0.le (by linarith), ?_⟩
  calc _ ≤ Real.log (Real.log (X ^ ((1 : ℝ) / 120))) := div_le_self hL0.le hlogL
    _ ≤ Real.log (Real.log X) := by
      have hX0 : 0 < X := by linarith
      have hlX : 0 < Real.log X := Real.log_pos hX
      apply Real.log_le_log (by linarith)
      rw [Real.log_rpow hX0]
      nlinarith

/-- `Y = o(log X)`. -/
theorem Ycut_littleO (ε : ℝ) (hε : 0 < ε) : ∃ X₀ : ℝ, ∀ X ≥ X₀, SV.Ycut X ≤ ε * Real.log X := by
  have h := (Real.isLittleO_log_id_atTop.comp_tendsto Real.tendsto_log_atTop).bound hε
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.1
    (h.and (eventually_Ycut_le_loglog.and (eventually_gt_atTop (1 : ℝ))))
  refine ⟨X₀, fun X hX => ?_⟩
  obtain ⟨h1, ⟨_, h2⟩, h3⟩ := hX₀ X hX
  simp only [Function.comp_apply, Real.norm_eq_abs, id] at h1
  have hlX : 0 < Real.log X := Real.log_pos h3
  rw [abs_of_pos hlX] at h1
  exact h2.trans ((le_abs_self _).trans h1)

/-- The period error is negligible: `K · 4^Y · Y^{c+1} ≤ X^a` for large `X`, when `Y = o(log X)`. -/
theorem eventually_err_small {Yf : ℝ → ℝ}
    (hlo : ∀ ε : ℝ, 0 < ε → ∃ X₀ : ℝ, ∀ X ≥ X₀, Yf X ≤ ε * Real.log X)
    (c K a : ℝ) (hc : 0 < c) (hK : 0 < K) (ha : 0 < a) :
    ∃ X₀ : ℝ, ∀ X ≥ X₀, 0 ≤ Yf X → K * ((4 : ℝ) ^ Yf X * Yf X ^ (c + 1)) ≤ X ^ a := by
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  obtain ⟨X₁, hX₁⟩ := hlo (a / (2 * Real.log 4)) (by positivity)
  obtain ⟨X₂, hX₂⟩ := hlo 1 one_pos
  have h3 := (isLittleO_log_rpow_rpow_atTop (c + 1) (by linarith : 0 < a / 2)).bound
    (by positivity : 0 < 1 / K)
  obtain ⟨X₃, hX₃⟩ := eventually_atTop.1 h3
  refine ⟨max (max X₁ X₂) (max X₃ 1), fun X hX hY => ?_⟩
  have hX1 : 1 ≤ X := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hX)
  have hX0 : 0 < X := by linarith
  have hlX : 0 ≤ Real.log X := Real.log_nonneg hX1
  have hYa := hX₁ X (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hX))
  have hYb := hX₂ X (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hX))
  have hc3 := hX₃ X (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hX))
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hlX _),
    abs_of_nonneg (Real.rpow_nonneg hX0.le _)] at hc3
  -- 4^Y ≤ X^{a/2}
  have h4 : (4 : ℝ) ^ Yf X ≤ X ^ (a / 2) := by
    rw [Real.rpow_def_of_pos (by norm_num), Real.rpow_def_of_pos hX0]
    apply Real.exp_le_exp.2
    have : Real.log 4 * Yf X ≤ Real.log 4 * (a / (2 * Real.log 4) * Real.log X) :=
      mul_le_mul_of_nonneg_left hYa hl4.le
    calc Real.log 4 * Yf X ≤ Real.log 4 * (a / (2 * Real.log 4) * Real.log X) := this
      _ = Real.log X * (a / 2) := by field_simp
  have h5 : Yf X ^ (c + 1) ≤ Real.log X ^ (c + 1) :=
    Real.rpow_le_rpow hY (by linarith) (by linarith)
  have h6 : K * Yf X ^ (c + 1) ≤ X ^ (a / 2) := by
    calc K * Yf X ^ (c + 1) ≤ K * Real.log X ^ (c + 1) := mul_le_mul_of_nonneg_left h5 hK.le
      _ ≤ K * (1 / K * X ^ (a / 2)) := mul_le_mul_of_nonneg_left hc3 hK.le
      _ = X ^ (a / 2) := by field_simp
  have h40 : 0 ≤ (4 : ℝ) ^ Yf X := Real.rpow_nonneg (by norm_num) _
  calc K * ((4 : ℝ) ^ Yf X * Yf X ^ (c + 1)) = (4 : ℝ) ^ Yf X * (K * Yf X ^ (c + 1)) := by ring
    _ ≤ X ^ (a / 2) * X ^ (a / 2) := mul_le_mul h4 h6 (by positivity) (Real.rpow_nonneg hX0.le _)
    _ = X ^ a := by rw [← Real.rpow_add hX0]; ring_nf

/-- `y# ≤ 4^y` (as reals). -/
theorem primorialR_le (y : ℝ) (hy : 0 ≤ y) : (primorialR y : ℝ) ≤ (4 : ℝ) ^ y := by
  unfold primorialR
  have h1 : ((primorial ⌊y⌋₊ : ℕ) : ℝ) ≤ ((4 ^ ⌊y⌋₊ : ℕ) : ℝ) := by
    exact_mod_cast primorial_le_four_pow _
  calc ((primorial ⌊y⌋₊ : ℕ) : ℝ) ≤ ((4 ^ ⌊y⌋₊ : ℕ) : ℝ) := h1
    _ = (4 : ℝ) ^ ((⌊y⌋₊ : ℕ) : ℝ) := by push_cast; rw [Real.rpow_natCast]
    _ ≤ (4 : ℝ) ^ y := Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.floor_le hy)

/-! ## Mertens' product theorem, in the two-sided form used -/

theorem Delta_nonneg (y : ℝ) : 0 ≤ Delta y := by
  unfold Delta
  refine Finset.prod_nonneg fun p hp => ?_
  have hp' := (Finset.mem_filter.1 hp).2
  have h1 : (1 : ℝ) ≤ p := by exact_mod_cast hp'.one_lt.le
  rw [sub_nonneg, div_le_one (by linarith)]
  exact h1

theorem mertens3_bounds (h3 : Principia.Erdos1054.Std_Mertens3) : ∃ y₀ : ℝ, ∀ y ≥ y₀,
    Real.exp (-eulerGamma) / 2 ≤ Delta y * Real.log y ∧
      Delta y * Real.log y ≤ Real.exp (-eulerGamma) + 1 := by
  have hpos : 0 < Real.exp (-eulerGamma) := Real.exp_pos _
  have h1 := h3.eventually (Icc_mem_nhds (by linarith : Real.exp (-eulerGamma) / 2 <
    Real.exp (-eulerGamma)) (by linarith : Real.exp (-eulerGamma) < Real.exp (-eulerGamma) + 1))
  obtain ⟨y₀, hy₀⟩ := eventually_atTop.1 h1
  exact ⟨y₀, fun y hy => Set.mem_Icc.1 (hy₀ y hy)⟩

/-! ## Reciprocal sums over a finite set of positive integers -/

theorem cnt_coe_finset (s : Finset ℕ) (hs1 : ∀ n ∈ s, 1 ≤ n) (m : ℕ) :
    cnt (↑s : Set ℕ) (m : ℝ) = (s.filter (· ≤ m)).card := by
  unfold cnt
  rw [Nat.floor_natCast]
  congr 1
  ext n
  rw [mem_cntFinset, Finset.mem_filter, Finset.mem_coe]
  constructor
  · rintro ⟨⟨_, h2⟩, h3⟩
    exact ⟨h3, h2⟩
  · rintro ⟨h3, h2⟩
    exact ⟨⟨hs1 n h3, h2⟩, h3⟩

theorem sum_inv_finset_eq (s : Finset ℕ) (N : ℕ) (hs : ∀ n ∈ s, 1 ≤ n ∧ n ≤ N) :
    ∑ n ∈ s, (1 : ℝ) / n = ((s.card : ℕ) : ℝ) / ((N : ℝ) + 1) +
      ∑ m ∈ Finset.Icc 1 N, (((s.filter (· ≤ m)).card : ℕ) : ℝ) / ((m : ℝ) * ((m : ℝ) + 1)) := by
  have hs1 : ∀ n ∈ s, 1 ≤ n := fun n hn => (hs n hn).1
  refine Eq.trans ?_ ((sum_inv_filter_eq (↑s : Set ℕ) N).trans ?_)
  · refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext n
    rw [mem_cntFinset, Finset.mem_coe]
    constructor
    · intro h
      exact ⟨hs n h, h⟩
    · intro h
      exact h.2
  · have hN : s.filter (· ≤ N) = s := Finset.filter_true_of_mem (fun n hn => (hs n hn).2)
    rw [cnt_coe_finset s hs1 N, hN]
    congr 1
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [cnt_coe_finset s hs1 m]

/-! ## `eq:sv-k-reciprocal` -/

end Principia.Erdos1054.Proofs.SvRegular

namespace Principia.Erdos1054.Proofs

open Finset Filter Principia.Erdos1054 Principia.Erdos1054.Proofs.SvRegular

/-- **`eq:sv-k-reciprocal`** (EP1054.tex lines 1545–1552), with the absolute constant
`C = e^{-γ} + 2`. -/
theorem link_Eq_SvKReciprocal : Principia.Erdos1054.Spine.Link_Eq_SvKReciprocal := by
  intro hPC h3
  obtain ⟨C₀, hC₀⟩ := hPC
  obtain ⟨y₀, hy₀⟩ := mertens3_bounds h3
  set K₁ := Real.exp (-eulerGamma) + 1 with hK₁
  have hK₁0 : 0 < K₁ := by positivity
  refine ⟨K₁ + 1, fun c hc => ?_⟩
  set C₀' := max C₀ 1 with hC₀'
  have hC₀'1 : 1 ≤ C₀' := le_max_right _ _
  obtain ⟨X₁, hX₁⟩ := eventually_err_small Ycut_littleO c C₀' (1 / 120) hc (by linarith)
    (by norm_num)
  obtain ⟨X₂, hX₂⟩ := eventually_atTop.1 (tendsto_Ycut.eventually_ge_atTop (max y₀ 2))
  obtain ⟨X₃, hX₃⟩ := eventually_atTop.1 (Real.tendsto_log_atTop.eventually_ge_atTop 3)
  refine ⟨max (max X₁ X₂) (max X₃ 1), fun X hX d hd1 hds hdc => ?_⟩
  have hXa : X₁ ≤ X := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hX)
  have hXb : X₂ ≤ X := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hX)
  have hXc : X₃ ≤ X := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hX)
  have hX1 : 1 ≤ X := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hX)
  have hX0 : 0 < X := by linarith
  set Y := SV.Ycut X with hYdef
  have hY : max y₀ 2 ≤ Y := hX₂ X hXb
  have hY2 : 2 ≤ Y := le_trans (le_max_right _ _) hY
  have hY0 : 0 < Y := by linarith
  have hlY : 0 < Real.log Y := Real.log_pos (by linarith)
  have hlX : 3 ≤ Real.log X := hX₃ X hXc
  have hM := (hy₀ Y (le_trans (le_max_left _ _) hY)).2
  have hΔ0 := Delta_nonneg Y
  have hΔ : Delta Y ≤ K₁ / Real.log Y := by rw [le_div_iff₀ hlY]; exact hM
  have hd0 : d ≠ 0 := by omega
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have hdpos : (0 : ℝ) < d := by linarith
  set P := primorialR Y with hPdef
  have hP0 : (0 : ℝ) ≤ P := Nat.cast_nonneg _
  -- the period count, one-sided
  have hcnt : ∀ T : ℝ, 0 ≤ T →
      (cnt {n : ℕ | SV.smoothPart Y n = d} T : ℝ) ≤ T / d * Delta Y + C₀' * P := by
    intro T hT
    have h := hC₀ Y T d hT hd1 hds
    have h' := (abs_le.1 h).2
    have : C₀ * (P : ℝ) ≤ C₀' * P := mul_le_mul_of_nonneg_right (le_max_left _ _) hP0
    linarith
  -- the error is small
  set U := X ^ ((1 : ℝ) / 120) with hUdef
  set U₀ := ⌊U⌋₊ with hU₀def
  have hU0 : 0 < U := Real.rpow_pos_of_pos hX0 _
  have hU₀1 : U < (U₀ : ℝ) + 1 := Nat.lt_floor_add_one U
  have herr := hX₁ X hXa hY0.le
  have hPle := primorialR_le Y hY0.le
  have hlogY_le : Real.log Y ≤ Y := (Real.log_le_sub_one_of_pos hY0).trans (by linarith)
  have hYc : Y ^ (c + 1) = Y ^ c * Y := Real.rpow_add_one hY0.ne' c
  have hYc0 : 0 ≤ Y ^ c := Real.rpow_nonneg hY0.le c
  have h4Y0 : 0 ≤ (4 : ℝ) ^ Y := Real.rpow_nonneg (by norm_num) _
  have hE : C₀' * P * ((d : ℝ) * Real.log Y) ≤ U := by
    calc C₀' * P * ((d : ℝ) * Real.log Y) ≤ C₀' * (4 : ℝ) ^ Y * (Y ^ c * Y) := by
          have h1 : (P : ℝ) * ((d : ℝ) * Real.log Y) ≤ (4 : ℝ) ^ Y * (Y ^ c * Y) :=
            mul_le_mul hPle (mul_le_mul hdc hlogY_le hlY.le hYc0) (by positivity) h4Y0
          calc C₀' * P * ((d : ℝ) * Real.log Y) = C₀' * (P * ((d : ℝ) * Real.log Y)) := by ring
            _ ≤ C₀' * ((4 : ℝ) ^ Y * (Y ^ c * Y)) := mul_le_mul_of_nonneg_left h1 (by linarith)
            _ = C₀' * (4 : ℝ) ^ Y * (Y ^ c * Y) := by ring
      _ = C₀' * ((4 : ℝ) ^ Y * Y ^ (c + 1)) := by rw [hYc]; ring
      _ ≤ U := herr
  set E := C₀' * P / ((U₀ : ℝ) + 1) with hEdef
  have hE0 : 0 ≤ E := by positivity
  have hEle : E ≤ 1 / ((d : ℝ) * Real.log Y) := by
    rw [hEdef, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
    linarith
  set B := Delta Y / d + E with hBdef
  have hB0 : 0 ≤ B := by positivity
  have hBle : B ≤ (K₁ + 1) / ((d : ℝ) * Real.log Y) := by
    have h1 : Delta Y / d ≤ K₁ / ((d : ℝ) * Real.log Y) := by
      rw [div_le_div_iff₀ hdpos (by positivity)]
      calc Delta Y * ((d : ℝ) * Real.log Y) = (d : ℝ) * (Delta Y * Real.log Y) := by ring
        _ ≤ (d : ℝ) * K₁ := mul_le_mul_of_nonneg_left hM hdpos.le
        _ = K₁ * d := by ring
    rw [hBdef, add_div]
    linarith
  -- Abel summation over the finite set `kSet X d`
  set V := X ^ ((1 : ℝ) / 60) with hVdef
  set N := ⌊V⌋₊ with hNdef
  have hUV : U ≤ V := Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num)
  have hU₀N : U₀ ≤ N := Nat.floor_mono hUV
  have hmem : ∀ n ∈ SV.kSet X d, 1 ≤ n ∧ n ≤ N ∧ U < (n : ℝ) ∧ SV.smoothPart Y n = d := by
    intro n hn
    rw [SV.kSet, Finset.mem_filter, Finset.mem_Iic] at hn
    refine ⟨?_, hn.1, hn.2.1, hn.2.2⟩
    have : (0 : ℝ) < n := lt_trans hU0 hn.2.1
    exact_mod_cast this
  rw [sum_inv_finset_eq (SV.kSet X d) N (fun n hn => ⟨(hmem n hn).1, (hmem n hn).2.1⟩)]
  -- the counting function of `kSet` is at most that of the class
  have hA : ∀ m : ℕ, ((((SV.kSet X d).filter (· ≤ m)).card : ℕ) : ℝ) ≤
      cnt {n : ℕ | SV.smoothPart Y n = d} (m : ℝ) := by
    intro m
    have : ((SV.kSet X d).filter (· ≤ m)).card ≤ cnt {n : ℕ | SV.smoothPart Y n = d} (m : ℝ) := by
      unfold cnt
      rw [Nat.floor_natCast]
      apply Finset.card_le_card
      intro n hn
      rw [Finset.mem_filter] at hn
      rw [mem_cntFinset]
      obtain ⟨h1, _, _, h4⟩ := hmem n hn.1
      exact ⟨⟨h1, hn.2⟩, h4⟩
    exact_mod_cast this
  have hA0 : ∀ m : ℕ, m ≤ U₀ → ((SV.kSet X d).filter (· ≤ m)).card = 0 := by
    intro m hm
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro n hn
    rw [Finset.mem_filter] at hn
    obtain ⟨_, _, h3, _⟩ := hmem n hn.1
    have h5 : (n : ℝ) ≤ U₀ := by exact_mod_cast hn.2.trans hm
    have h6 : (U₀ : ℝ) ≤ U := Nat.floor_le hU0.le
    linarith
  -- first term
  have hfirst : (((SV.kSet X d).card : ℕ) : ℝ) / ((N : ℝ) + 1) ≤ B := by
    have hc1 : (((SV.kSet X d).card : ℕ) : ℝ) ≤ (N : ℝ) / d * Delta Y + C₀' * P := by
      have := hA N
      rw [Finset.filter_true_of_mem (fun n hn => (hmem n hn).2.1)] at this
      exact this.trans (hcnt N (Nat.cast_nonneg N))
    have hNU : (U₀ : ℝ) + 1 ≤ (N : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hU₀N
    rw [div_le_iff₀ (by positivity)]
    have h1 : C₀' * P ≤ E * ((N : ℝ) + 1) := by
      rw [hEdef, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      have : 0 ≤ C₀' * (P : ℝ) := by positivity
      exact mul_le_mul_of_nonneg_left hNU this
    have h2 : (N : ℝ) / d * Delta Y ≤ Delta Y / d * ((N : ℝ) + 1) := by
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hdpos]
      have : Delta Y * ((N : ℝ) + 1) = (N : ℝ) * Delta Y + Delta Y := by ring
      linarith
    have e3 : B * ((N : ℝ) + 1) = Delta Y / d * ((N : ℝ) + 1) + E * ((N : ℝ) + 1) := by
      rw [hBdef]; ring
    linarith
  -- per-term bound
  have hterm : ∀ m ∈ Finset.Icc 1 N,
      (((SV.kSet X d).filter (· ≤ m)).card : ℝ) / ((m : ℝ) * ((m : ℝ) + 1)) ≤
        B * (1 / (m : ℝ)) := by
    intro m hm
    have hm1 : 1 ≤ m := (Finset.mem_Icc.1 hm).1
    have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm1
    have hden : (0 : ℝ) < (m : ℝ) * ((m : ℝ) + 1) := by positivity
    by_cases hmU : m ≤ U₀
    · rw [hA0 m hmU, Nat.cast_zero, zero_div]
      positivity
    · push Not at hmU
      have hmU' : (U₀ : ℝ) + 1 ≤ m := by exact_mod_cast hmU
      have hc1 := (hA m).trans (hcnt m (Nat.cast_nonneg m))
      rw [div_le_iff₀ hden]
      have he : B * (1 / (m : ℝ)) * ((m : ℝ) * ((m : ℝ) + 1)) =
          Delta Y / d * ((m : ℝ) + 1) + E * ((m : ℝ) + 1) := by
        rw [hBdef]
        field_simp
      rw [he]
      have h1 : C₀' * P ≤ E * ((m : ℝ) + 1) := by
        rw [hEdef, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
        have : 0 ≤ C₀' * (P : ℝ) := by positivity
        exact mul_le_mul_of_nonneg_left (by linarith) this
      have h2 : (m : ℝ) / d * Delta Y ≤ Delta Y / d * ((m : ℝ) + 1) := by
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hdpos]
        have : Delta Y * ((m : ℝ) + 1) = (m : ℝ) * Delta Y + Delta Y := by ring
        linarith
      linarith
  have hsum := Finset.sum_le_sum hterm
  rw [← Finset.mul_sum] at hsum
  have hH := sum_Icc_inv_le_one_add_log N
  have hlogN : Real.log N ≤ Real.log X / 60 := by
    rcases Nat.eq_zero_or_pos N with h0 | hpos
    · rw [h0, Nat.cast_zero, Real.log_zero]
      linarith
    · have h1 : Real.log N ≤ Real.log V :=
        Real.log_le_log (by exact_mod_cast hpos) (Nat.floor_le (Real.rpow_nonneg hX0.le _))
      rw [hVdef, Real.log_rpow hX0] at h1
      linarith
  have hBH : B * ∑ i ∈ Finset.Icc 1 N, (1 : ℝ) / i ≤ B * (1 + Real.log X / 60) :=
    mul_le_mul_of_nonneg_left (hH.trans (by linarith)) hB0
  have htot : B * (2 + Real.log X / 60) ≤ (K₁ + 1) / ((d : ℝ) * Real.log Y) * Real.log X := by
    have h1 : 2 + Real.log X / 60 ≤ Real.log X := by linarith
    calc B * (2 + Real.log X / 60) ≤ B * Real.log X := mul_le_mul_of_nonneg_left h1 hB0
      _ ≤ (K₁ + 1) / ((d : ℝ) * Real.log Y) * Real.log X :=
          mul_le_mul_of_nonneg_right hBle (by linarith)
  have hgoal : (K₁ + 1) / ((d : ℝ) * Real.log Y) * Real.log X =
      (K₁ + 1) * (Real.log X / ((d : ℝ) * Real.log Y)) := by ring
  rw [← hgoal]
  have e1 : B * (2 + Real.log X / 60) = B + B * (1 + Real.log X / 60) := by ring
  linarith

end Principia.Erdos1054.Proofs

namespace Principia.Erdos1054.Proofs.SvRegular

open Finset Filter Principia.Erdos1054

/-! ## Reciprocal prime sums over power intervals -/

/-- `∑_{p ≤ x} 1/p = ∑_{a < p ≤ b} 1/p + ∑_{p ≤ a} 1/p` for `0 ≤ a ≤ b`. -/
theorem sum_primes_split {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∑ p ∈ (Finset.Iic ⌊b⌋₊).filter Nat.Prime, (1 : ℝ) / p =
      ∑ p ∈ SV.primesIoc a b, (1 : ℝ) / p +
        ∑ p ∈ (Finset.Iic ⌊a⌋₊).filter Nat.Prime, (1 : ℝ) / p := by
  rw [← Finset.sum_filter_add_sum_filter_not ((Finset.Iic ⌊b⌋₊).filter Nat.Prime)
    (fun p : ℕ => a < (p : ℝ))]
  congr 1
  · refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext p
    simp only [SV.primesIoc, Finset.mem_filter, Finset.mem_Iic]
    tauto
  · refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext p
    simp only [Finset.mem_filter, Finset.mem_Iic, not_lt]
    constructor
    · rintro ⟨⟨_, h2⟩, h3⟩
      exact ⟨Nat.le_floor h3, h2⟩
    · rintro ⟨h1, h2⟩
      have h3 : (p : ℝ) ≤ a := (Nat.cast_le.2 h1).trans (Nat.floor_le ha)
      exact ⟨⟨Nat.le_floor (h3.trans hab), h2⟩, h3⟩

/-- Mertens' second theorem bounds the reciprocal prime sum over `(X^{θ₁}, X^{θ₂}]` by `θ₂/θ₁`
for large `X`. -/
theorem primesIoc_recip_le (h2 : Principia.Erdos1054.Std_Mertens2) (θ₁ θ₂ : ℝ) (h1 : 0 < θ₁)
    (h12 : θ₁ ≤ θ₂) :
    ∃ X₀ : ℝ, ∀ X ≥ X₀, ∑ p ∈ SV.primesIoc (X ^ θ₁) (X ^ θ₂), (1 : ℝ) / p ≤ θ₂ / θ₁ := by
  obtain ⟨M, C, hM⟩ := h2
  obtain ⟨X₁, hX₁⟩ := eventually_atTop.1 ((tendsto_rpow_atTop h1).eventually_ge_atTop 2)
  obtain ⟨X₂, hX₂⟩ := eventually_atTop.1
    (Real.tendsto_log_atTop.eventually_ge_atTop (2 * |C| / θ₁ + 1))
  refine ⟨max (max X₁ X₂) 1, fun X hX => ?_⟩
  have hX1 : 1 ≤ X := le_trans (le_max_right _ _) hX
  have hX0 : 0 < X := by linarith
  have ha2 : 2 ≤ X ^ θ₁ := hX₁ X (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hX))
  have hlX : 2 * |C| / θ₁ + 1 ≤ Real.log X :=
    hX₂ X (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hX))
  have hC0 : 0 ≤ 2 * |C| / θ₁ := by positivity
  have hlX0 : 0 < Real.log X := by linarith
  have hab : X ^ θ₁ ≤ X ^ θ₂ := Real.rpow_le_rpow_of_exponent_le hX1 h12
  have hb2 : 2 ≤ X ^ θ₂ := ha2.trans hab
  have hsplit := sum_primes_split (by linarith : (0 : ℝ) ≤ X ^ θ₁) hab
  have hMb := (abs_le.1 (hM (X ^ θ₂) hb2)).2
  have hMa := (abs_le.1 (hM (X ^ θ₁) ha2)).1
  have hla : Real.log (X ^ θ₁) = θ₁ * Real.log X := Real.log_rpow hX0 θ₁
  have hlb : Real.log (X ^ θ₂) = θ₂ * Real.log X := Real.log_rpow hX0 θ₂
  have hla0 : 0 < θ₁ * Real.log X := by positivity
  have hlb0 : 0 < θ₂ * Real.log X := by nlinarith
  rw [hla] at hMa
  rw [hlb] at hMb
  -- log log b − log log a = log(θ₂/θ₁) ≤ θ₂/θ₁ − 1
  have hll : Real.log (θ₂ * Real.log X) - Real.log (θ₁ * Real.log X) ≤ θ₂ / θ₁ - 1 := by
    rw [← Real.log_div hlb0.ne' hla0.ne']
    have : θ₂ * Real.log X / (θ₁ * Real.log X) = θ₂ / θ₁ := by field_simp
    rw [this]
    exact Real.log_le_sub_one_of_pos (div_pos (by linarith) h1)
  -- the error terms
  have hCb : C / (θ₂ * Real.log X) ≤ |C| / (θ₁ * Real.log X) := by
    calc C / (θ₂ * Real.log X) ≤ |C| / (θ₂ * Real.log X) :=
          div_le_div_of_nonneg_right (le_abs_self C) hlb0.le
      _ ≤ |C| / (θ₁ * Real.log X) :=
          div_le_div_of_nonneg_left (abs_nonneg C) hla0 (by nlinarith)
  have hCa : C / (θ₁ * Real.log X) ≤ |C| / (θ₁ * Real.log X) :=
    div_le_div_of_nonneg_right (le_abs_self C) hla0.le
  have hCt : 2 * (|C| / (θ₁ * Real.log X)) ≤ 1 := by
    rw [← mul_div_assoc, div_le_one hla0]
    have := mul_le_mul_of_nonneg_left hlX h1.le
    have e : θ₁ * (2 * |C| / θ₁ + 1) = 2 * |C| + θ₁ := by field_simp
    linarith
  linarith

end Principia.Erdos1054.Proofs.SvRegular

namespace Principia.Erdos1054.Proofs

open Finset Filter Principia.Erdos1054 Principia.Erdos1054.Proofs.SvRegular

/-- **`eq:sv-m-reciprocal`** (EP1054.tex lines 1553–1558). -/
theorem link_Eq_SvMReciprocal : Principia.Erdos1054.Spine.Link_Eq_SvMReciprocal := by
  intro hK h2
  obtain ⟨CK, hCK⟩ := hK
  obtain ⟨Xq, hXq⟩ := primesIoc_recip_le h2 (7 / 20) (11 / 30) (by norm_num) (by norm_num)
  obtain ⟨Xr, hXr⟩ := primesIoc_recip_le h2 (1 / 15) (1 / 12) (by norm_num) (by norm_num)
  refine ⟨(11 / 30) / (7 / 20) * ((1 / 12) / (1 / 15)) * CK, fun c hc => ?_⟩
  obtain ⟨Xk, hXk⟩ := hCK c hc
  refine ⟨max Xk (max Xq Xr), fun X hX d hd1 hds hdc => ?_⟩
  have hk := hXk X (le_trans (le_max_left _ _) hX) d hd1 hds hdc
  have hq := hXq X (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hX))
  have hr := hXr X (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hX))
  have e : ∀ q r k : ℕ, (1 : ℝ) / ((q : ℝ) * (r : ℝ) * (k : ℝ)) = 1 / q * (1 / r * (1 / k)) := by
    intro q r k
    rw [one_div, one_div, one_div, one_div, mul_inv, mul_inv, mul_assoc]
  simp_rw [e, ← Finset.mul_sum, ← Finset.sum_mul]
  have hq0 : 0 ≤ ∑ q ∈ SV.primesIoc (X ^ ((7 : ℝ) / 20)) (X ^ ((11 : ℝ) / 30)), (1 : ℝ) / q :=
    Finset.sum_nonneg (fun _ _ => by positivity)
  have hr0 : 0 ≤ ∑ r ∈ SV.primesIoc (X ^ ((1 : ℝ) / 15)) (X ^ ((1 : ℝ) / 12)), (1 : ℝ) / r :=
    Finset.sum_nonneg (fun _ _ => by positivity)
  have hk0 : 0 ≤ ∑ k ∈ SV.kSet X d, (1 : ℝ) / k := Finset.sum_nonneg (fun _ _ => by positivity)
  set Sq := ∑ q ∈ SV.primesIoc (X ^ ((7 : ℝ) / 20)) (X ^ ((11 : ℝ) / 30)), (1 : ℝ) / q
  set Sr := ∑ r ∈ SV.primesIoc (X ^ ((1 : ℝ) / 15)) (X ^ ((1 : ℝ) / 12)), (1 : ℝ) / r
  set Sk := ∑ k ∈ SV.kSet X d, (1 : ℝ) / k
  set Q := Real.log X / ((d : ℝ) * Real.log (SV.Ycut X))
  calc Sq * (Sr * Sk) ≤ (11 / 30) / (7 / 20) * (Sr * Sk) :=
        mul_le_mul_of_nonneg_right hq (by positivity)
    _ ≤ (11 / 30) / (7 / 20) * ((1 / 12) / (1 / 15) * Sk) := by
        gcongr
    _ ≤ (11 / 30) / (7 / 20) * ((1 / 12) / (1 / 15) * (CK * Q)) := by
        gcongr
    _ = (11 / 30) / (7 / 20) * ((1 / 12) / (1 / 15)) * CK * Q := by ring

end Principia.Erdos1054.Proofs

namespace Principia.Erdos1054.Proofs.SvRegular

open Finset Filter Principia.Erdos1054

/-! ## Legendre's formula for the smooth parts, and Markov's inequality -/

/-- The logarithm of a `y`-smooth divisor `m` of `K ≠ 0` is at most `∑_{p ≤ y} v_p(K) log p`. -/
theorem log_smooth_dvd_le {y : ℝ} {m K : ℕ} (hK : K ≠ 0) (hmK : m ∣ K) (hm : IsSmooth y m) :
    Real.log m ≤
      ∑ p ∈ (Finset.Iic ⌊y⌋₊).filter Nat.Prime, (K.factorization p : ℝ) * Real.log p := by
  have hm0 : m ≠ 0 := ne_zero_of_dvd_ne_zero hK hmK
  rw [Real.log_nat_eq_sum_factorization, Finsupp.sum, Nat.support_factorization]
  calc ∑ p ∈ m.primeFactors, (m.factorization p : ℝ) * Real.log p
      ≤ ∑ p ∈ m.primeFactors, (K.factorization p : ℝ) * Real.log p := by
        apply Finset.sum_le_sum
        intro p _
        apply mul_le_mul_of_nonneg_right _ (Real.log_natCast_nonneg p)
        exact_mod_cast (Nat.factorization_le_iff_dvd hm0 hK).2 hmK p
    _ ≤ ∑ p ∈ (Finset.Iic ⌊y⌋₊).filter Nat.Prime, (K.factorization p : ℝ) * Real.log p := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro p hp
          rw [Finset.mem_filter, Finset.mem_Iic]
          exact ⟨Nat.le_floor (hm p hp), (Nat.mem_primeFactors.1 hp).1⟩
        · intro p _ _
          exact mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg p)

/-- Legendre: `v_p(N!) ≤ N/(p − 1)`. -/
theorem factorization_factorial_le {p : ℕ} (hp : p.Prime) (N : ℕ) :
    ((N.factorial).factorization p : ℝ) ≤ (N : ℝ) / ((p : ℝ) - 1) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  rw [le_div_iff₀ (by linarith)]
  rcases Nat.eq_zero_or_pos N with h0 | hN
  · subst h0
    simp
  · haveI := Fact.mk hp
    have h := sub_one_mul_padicValNat_factorial_lt_of_ne_zero p (Nat.pos_iff_ne_zero.1 hN)
    rw [← Nat.factorization_def _ hp] at h
    have h'' : ((p - 1 : ℕ) : ℝ) * ((N.factorial).factorization p : ℝ) ≤ N := by
      exact_mod_cast h.le
    have e : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
      rw [Nat.cast_sub hp.one_lt.le, Nat.cast_one]
    rw [e] at h''
    linarith

/-- `∑_{n ≤ N} log D_y(n) ≤ N ∑_{p ≤ y} log p/(p − 1)` (EP1054.tex lines 1377–1381). -/
theorem sum_log_smoothPart_le (y : ℝ) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, Real.log (SV.smoothPart y n) ≤
      N * ∑ p ∈ (Finset.Iic ⌊y⌋₊).filter Nat.Prime, Real.log p / ((p : ℝ) - 1) := by
  have hn0 : ∀ n ∈ Finset.Icc 1 N, n ≠ 0 := fun n hn => by
    have := (Finset.mem_Icc.1 hn).1
    omega
  have hlog : ∑ n ∈ Finset.Icc 1 N, Real.log (SV.smoothPart y n) =
      Real.log ((∏ n ∈ Finset.Icc 1 N, SV.smoothPart y n : ℕ) : ℝ) := by
    rw [Nat.cast_prod, Real.log_prod]
    intro n hn
    exact_mod_cast smoothPart_ne_zero (hn0 n hn)
  have hdvd : (∏ n ∈ Finset.Icc 1 N, SV.smoothPart y n) ∣ N.factorial := by
    have : ∏ n ∈ Finset.Icc 1 N, n = N.factorial := by
      rw [← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_id_eq_factorial]
    rw [← this]
    exact Finset.prod_dvd_prod_of_dvd _ _ (fun n hn => (smoothPart_spec (hn0 n hn)).1)
  have hsm : IsSmooth y (∏ n ∈ Finset.Icc 1 N, SV.smoothPart y n) :=
    Finset.prod_induction _ (IsSmooth y) (fun a b ha hb => isSmooth_mul ha hb) (isSmooth_one y)
      (fun n hn => (smoothPart_spec (hn0 n hn)).2)
  rw [hlog]
  refine (log_smooth_dvd_le (Nat.factorial_ne_zero N) hdvd hsm).trans ?_
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hp' := (Finset.mem_filter.1 hp).2
  have h1 := factorization_factorial_le hp' N
  have hlp : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  calc (N.factorial.factorization p : ℝ) * Real.log p ≤ N / ((p : ℝ) - 1) * Real.log p :=
        mul_le_mul_of_nonneg_right h1 hlp
    _ = N * (Real.log p / ((p : ℝ) - 1)) := by ring

/-- Markov's inequality for `log D_y` (EP1054.tex lines 1384–1387). -/
theorem cnt_smoothPart_large_le {y c : ℝ} (hy : 1 < y) (X : ℝ) :
    (cnt {n : ℕ | y ^ c < (SV.smoothPart y n : ℝ)} X : ℝ) * (c * Real.log y) ≤
      ⌊X⌋₊ * ∑ p ∈ (Finset.Iic ⌊y⌋₊).filter Nat.Prime, Real.log p / ((p : ℝ) - 1) := by
  have hy0 : 0 < y := by linarith
  unfold cnt
  rw [← nsmul_eq_mul]
  refine (Finset.card_nsmul_le_sum _ (fun n => Real.log (SV.smoothPart y n)) (c * Real.log y)
    ?_).trans ?_
  · intro n hn
    rw [mem_cntFinset] at hn
    have h : y ^ c < (SV.smoothPart y n : ℝ) := hn.2
    have h2 := Real.log_lt_log (Real.rpow_pos_of_pos hy0 c) h
    rw [Real.log_rpow hy0] at h2
    exact h2.le
  · refine (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun n _ _ => Real.log_natCast_nonneg _)).trans ?_
    exact sum_log_smoothPart_le y ⌊X⌋₊

end Principia.Erdos1054.Proofs.SvRegular

namespace Principia.Erdos1054.Proofs

open Finset Filter Principia.Erdos1054 Principia.Erdos1054.Proofs.SvRegular

/-- **`lem:smooth-part-input`** (EP1054.tex lines 1348–1389). -/
theorem link_Lem_SmoothPartInput : Principia.Erdos1054.Spine.Link_Lem_SmoothPartInput := by
  intro hPC h1 h3 Yf hYf hlo
  obtain ⟨C₀, hC₀⟩ := hPC
  obtain ⟨y₀, hy₀⟩ := mertens3_bounds h3
  obtain ⟨C₁, hC₁⟩ := h1
  set a₀ := Real.exp (-eulerGamma) / 2 with ha₀def
  set K₁ := Real.exp (-eulerGamma) + 1 with hK₁def
  have ha₀ : 0 < a₀ := by positivity
  have hK₁ : 0 < K₁ := by positivity
  set C₀' := max C₀ 1 with hC₀'
  have hC₀'1 : 1 ≤ C₀' := le_max_right _ _
  refine ⟨?_, ?_⟩
  · intro c hc
    obtain ⟨X₁, hX₁⟩ := eventually_err_small hlo c (2 * C₀' / a₀) 1 hc (by positivity) one_pos
    obtain ⟨X₂, hX₂⟩ := eventually_atTop.1 (hYf.eventually_ge_atTop (max y₀ 2))
    refine ⟨a₀ / 2, K₁ + a₀ / 2, by positivity, by positivity, max (max X₁ X₂) 0,
      fun X hX d hd1 hds hdc => ?_⟩
    have hXa : X₁ ≤ X := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hX)
    have hXb : X₂ ≤ X := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hX)
    have hX0 : 0 ≤ X := le_trans (le_max_right _ _) hX
    set Y := Yf X with hYdef
    have hY : max y₀ 2 ≤ Y := hX₂ X hXb
    have hY2 : 2 ≤ Y := le_trans (le_max_right _ _) hY
    have hY0 : 0 < Y := by linarith
    have hlY : 0 < Real.log Y := Real.log_pos (by linarith)
    have hMb := hy₀ Y (le_trans (le_max_left _ _) hY)
    have hd0 : d ≠ 0 := by omega
    have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd1
    have hdpos : (0 : ℝ) < d := by linarith
    set P := primorialR Y with hPdef
    have hP0 : (0 : ℝ) ≤ P := Nat.cast_nonneg _
    have hper := hC₀ Y X d hX0 hd1 hds
    have hCP : C₀ * (P : ℝ) ≤ C₀' * P := mul_le_mul_of_nonneg_right (le_max_left _ _) hP0
    -- error
    have herr := hX₁ X hXa hY0.le
    rw [Real.rpow_one] at herr
    have hPle := primorialR_le Y hY0.le
    have hlogY_le : Real.log Y ≤ Y := (Real.log_le_sub_one_of_pos hY0).trans (by linarith)
    have hYc : Y ^ (c + 1) = Y ^ c * Y := Real.rpow_add_one hY0.ne' c
    have hYc0 : 0 ≤ Y ^ c := Real.rpow_nonneg hY0.le c
    have h4Y0 : 0 ≤ (4 : ℝ) ^ Y := Real.rpow_nonneg (by norm_num) _
    have hPd : (P : ℝ) * ((d : ℝ) * Real.log Y) ≤ (4 : ℝ) ^ Y * Y ^ (c + 1) := by
      rw [hYc]
      exact mul_le_mul hPle (mul_le_mul hdc hlogY_le hlY.le hYc0) (by positivity) h4Y0
    set Q := X / ((d : ℝ) * Real.log Y) with hQdef
    have hQ0 : 0 ≤ Q := by positivity
    have hdl : (0 : ℝ) < (d : ℝ) * Real.log Y := by positivity
    have hE : C₀' * P ≤ a₀ / 2 * Q := by
      rw [hQdef, mul_div_assoc', le_div_iff₀ hdl]
      have e1 : 2 * C₀' / a₀ * ((4 : ℝ) ^ Y * Y ^ (c + 1)) * (a₀ / 2) =
          C₀' * ((4 : ℝ) ^ Y * Y ^ (c + 1)) := by field_simp
      calc C₀' * P * ((d : ℝ) * Real.log Y) = C₀' * (P * ((d : ℝ) * Real.log Y)) := by ring
        _ ≤ C₀' * ((4 : ℝ) ^ Y * Y ^ (c + 1)) := mul_le_mul_of_nonneg_left hPd (by linarith)
        _ = 2 * C₀' / a₀ * ((4 : ℝ) ^ Y * Y ^ (c + 1)) * (a₀ / 2) := e1.symm
        _ ≤ X * (a₀ / 2) := mul_le_mul_of_nonneg_right herr (by positivity)
        _ = a₀ / 2 * X := by ring
    have hmain : X / d * Delta Y = Q * (Delta Y * Real.log Y) := by
      rw [hQdef]
      field_simp
    have hlo1 : a₀ * Q ≤ X / d * Delta Y := by
      rw [hmain, mul_comm a₀ Q]
      exact mul_le_mul_of_nonneg_left hMb.1 hQ0
    have hhi1 : X / d * Delta Y ≤ K₁ * Q := by
      rw [hmain, mul_comm K₁ Q]
      exact mul_le_mul_of_nonneg_left hMb.2 hQ0
    have hab := abs_le.1 hper
    constructor
    · show a₀ / 2 * Q ≤ _
      linarith
    · show _ ≤ (K₁ + a₀ / 2) * Q
      linarith
  · intro η hη
    refine ⟨|C₁| / η + 1, by positivity, fun c hc => ?_⟩
    obtain ⟨X₂, hX₂⟩ := eventually_atTop.1 (hYf.eventually_ge_atTop 2)
    refine ⟨max X₂ 0, fun X hX => ?_⟩
    have hX0 : 0 ≤ X := le_trans (le_max_right _ _) hX
    have hY2 : 2 ≤ Yf X := hX₂ X (le_trans (le_max_left _ _) hX)
    have hlY : 0 < Real.log (Yf X) := Real.log_pos (by linarith)
    have hc0 : 0 < c := lt_of_lt_of_le (by positivity) hc
    have hM := cnt_smoothPart_large_le (c := c) (by linarith : 1 < Yf X) X
    have hM1 := hC₁ (Yf X) hY2
    have hN0 : (0 : ℝ) ≤ (⌊X⌋₊ : ℝ) := Nat.cast_nonneg _
    have hNX : (⌊X⌋₊ : ℝ) ≤ X := Nat.floor_le hX0
    have hC1c : |C₁| ≤ c * η := by
      have : |C₁| / η ≤ c := by linarith
      rwa [div_le_iff₀ hη] at this
    have h2 : (⌊X⌋₊ : ℝ) * ∑ p ∈ (Finset.Iic ⌊Yf X⌋₊).filter Nat.Prime,
        Real.log p / ((p : ℝ) - 1) ≤ (η * ⌊X⌋₊) * (c * Real.log (Yf X)) := by
      calc (⌊X⌋₊ : ℝ) * ∑ p ∈ (Finset.Iic ⌊Yf X⌋₊).filter Nat.Prime, Real.log p / ((p : ℝ) - 1)
          ≤ (⌊X⌋₊ : ℝ) * (C₁ * Real.log (Yf X)) := mul_le_mul_of_nonneg_left hM1 hN0
        _ ≤ (⌊X⌋₊ : ℝ) * (|C₁| * Real.log (Yf X)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_abs_self C₁) hlY.le) hN0
        _ ≤ (⌊X⌋₊ : ℝ) * ((c * η) * Real.log (Yf X)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hC1c hlY.le) hN0
        _ = (η * ⌊X⌋₊) * (c * Real.log (Yf X)) := by ring
    have h3 := le_of_mul_le_mul_right (hM.trans h2) (by positivity)
    calc _ ≤ η * (⌊X⌋₊ : ℝ) := h3
      _ ≤ η * X := mul_le_mul_of_nonneg_left hNX hη.le

end Principia.Erdos1054.Proofs

namespace Principia.Erdos1054.Proofs.SvRegular

open Finset Filter Principia.Erdos1054

/-! ## `∑_{P^+(d) ≤ y} 1/d ≤ ∏_{p ≤ y} (1 − 1/p)^{-1}` -/

/-- `n ↦ 1/n` as a monoid hom `ℕ →* ℝ`. -/
noncomputable def invHom : ℕ →* ℝ where
  toFun n := (n : ℝ)⁻¹
  map_one' := by simp
  map_mul' a b := by
    push_cast
    rw [mul_inv]

/-- The reciprocal sum over any finite set of `y`-smooth positive integers is at most
`Δ(y)⁻¹ = ∏_{p ≤ y} (1 − 1/p)^{-1}` (EP1054.tex lines 1509–1511). -/
theorem sum_inv_smooth_le (y : ℝ) (s : Finset ℕ)
    (hs : ∀ d ∈ s, d ≠ 0 ∧ IsSmooth y d) : ∑ d ∈ s, (1 : ℝ) / d ≤ (Delta y)⁻¹ := by
  classical
  have hf : ∀ {p : ℕ}, p.Prime → ‖invHom p‖ < 1 := by
    intro p hp
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    show ‖(p : ℝ)⁻¹‖ < 1
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact inv_lt_one_of_one_lt₀ (by linarith)
  have hsum := (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric hf
    (⌊y⌋₊ + 1)).2
  have hmem : ∀ d ∈ s, d ∈ Nat.smoothNumbers (⌊y⌋₊ + 1) := by
    intro d hd
    rw [Nat.mem_smoothNumbers]
    refine ⟨(hs d hd).1, fun p hp => ?_⟩
    rw [Nat.mem_primeFactorsList'] at hp
    have hp2 : p ∈ d.primeFactors := Nat.mem_primeFactors.2 hp
    have := (hs d hd).2 p hp2
    exact Nat.lt_succ_of_le (Nat.le_floor this)
  have hsub := Finset.sum_subtype_of_mem (fun d : ℕ => (1 : ℝ) / d) hmem
  rw [← hsub]
  have hle := sum_le_hasSum (s.subtype (· ∈ Nat.smoothNumbers (⌊y⌋₊ + 1)))
    (fun i _ => by show (0 : ℝ) ≤ ((i : ℕ) : ℝ)⁻¹; positivity) hsum
  have heq : ∏ p ∈ (⌊y⌋₊ + 1).primesBelow, (1 - invHom p)⁻¹ = (Delta y)⁻¹ := by
    unfold Delta
    rw [← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl (fun p _ => ?_)
    rw [one_div]
    rfl
  rw [heq] at hle
  refine le_trans (le_of_eq ?_) hle
  refine Finset.sum_congr rfl (fun i _ => ?_)
  show (1 : ℝ) / ((i : ℕ) : ℝ) = ((i : ℕ) : ℝ)⁻¹
  rw [one_div]

/-! ## `lem:sv-classes` -/

open Classical in
theorem mem_A0 {D M : ℕ} {X : ℝ} (h : M ∈ S4a.A0 D X) :
    (1 ≤ M ∧ M ≤ ⌊X⌋₊) ∧ ∃ p q r k : ℕ, S4a.A0Tuple D X p q r k ∧ M = p * q * r * k := by
  unfold S4a.A0 at h
  rw [Finset.mem_filter, Finset.mem_Icc] at h
  exact h

/-- A finset inside `[1, X]` has at most `cnt` members in any set. -/
theorem card_filter_le_cnt {A : Finset ℕ} {X : ℝ} (hA : ∀ M ∈ A, 1 ≤ M ∧ M ≤ ⌊X⌋₊)
    (P : ℕ → Prop) [DecidablePred P] : (A.filter P).card ≤ cnt {n : ℕ | P n} X := by
  unfold cnt
  apply Finset.card_le_card
  intro M hM
  rw [Finset.mem_filter] at hM
  rw [mem_cntFinset]
  exact ⟨hA M hM.1, hM.2⟩

end Principia.Erdos1054.Proofs.SvRegular

namespace Principia.Erdos1054.Proofs

open Finset Filter Principia.Erdos1054 Principia.Erdos1054.Proofs.SvRegular

/-- **`lem:sv-classes`** (EP1054.tex lines 1486–1527). -/
theorem link_Lem_SvClasses : Principia.Erdos1054.Spine.Link_Lem_SvClasses := by
  intro hSPI h3 δ _ _ D _ 𝒜 h𝒜
  obtain ⟨cF, hcF, B, _, XF, hXF⟩ := h𝒜
  obtain ⟨hsize, htail⟩ := hSPI SV.Ycut tendsto_Ycut Ycut_littleO
  obtain ⟨c, hc, hct⟩ := htail (cF / 3) (by positivity)
  obtain ⟨Xt, hXt⟩ := hct c le_rfl
  obtain ⟨c₁', c₂, _, hc₂, Xs, hXs⟩ := hsize c hc
  obtain ⟨y₀, hy₀⟩ := mertens3_bounds h3
  set a₀ := Real.exp (-eulerGamma) / 2 with ha₀def
  have ha₀ : 0 < a₀ := by positivity
  obtain ⟨XY, hXY⟩ := eventually_atTop.1 (tendsto_Ycut.eventually_ge_atTop (max y₀ 2))
  set a := cF * a₀ / 3 with hadef
  have ha : 0 < a := by positivity
  refine ⟨c, a, c₂, cF / (3 * c₂), hc, ha, hc₂, by positivity,
    max (max XF Xt) (max (max Xs XY) 1), fun X hX => ?_⟩
  have hX1 : XF ≤ X := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hX)
  have hX2 : Xt ≤ X := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hX)
  have hX3 : Xs ≤ X :=
    le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hX))
  have hX4 : XY ≤ X :=
    le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hX))
  have hX5 : 1 ≤ X := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hX)
  have hX0 : 0 < X := by linarith
  obtain ⟨hsub, hcard, hreg⟩ := hXF X hX1
  set Y := SV.Ycut X with hYdef
  have hY : max y₀ 2 ≤ Y := hXY X hX4
  have hY2 : 2 ≤ Y := le_trans (le_max_right _ _) hY
  have hY0 : 0 < Y := by linarith
  have hlY : 0 < Real.log Y := Real.log_pos (by linarith)
  have hMY := (hy₀ Y (le_trans (le_max_left _ _) hY)).1
  set A := 𝒜 X with hAdef
  have hA : ∀ M ∈ A, 1 ≤ M ∧ M ≤ ⌊X⌋₊ := fun M hM => (mem_A0 (hsub hM)).1
  have hA0 : ∀ M ∈ A, M ≠ 0 := fun M hM => by
    have := (hA M hM).1
    omega
  -- `D_Y(s(M)) = D_Y(M)` for members (property (i) at `t = M`)
  have hsa : ∀ M ∈ A, SV.smoothPart Y (aliquot M) = SV.smoothPart Y M := by
    intro M hM
    obtain ⟨p, q, r, k, ht, hMe⟩ := (mem_A0 (hsub hM)).2
    exact ((hreg M hM p q r k ht hMe).2.2.2.1.2.2.1).symm
  set I := A.image (SV.smoothPart Y) with hIdef
  have hI : ∀ d ∈ I, d ≠ 0 ∧ IsSmooth Y d := by
    intro d hd
    obtain ⟨M, hM, rfl⟩ := Finset.mem_image.1 hd
    exact ⟨smoothPart_ne_zero (hA0 M hM), (smoothPart_spec (hA0 M hM)).2⟩
  set I₁ := I.filter (fun d : ℕ => (d : ℝ) ≤ Y ^ c) with hI₁def
  set 𝒟 := I₁.filter (fun d : ℕ => a * (X / ((d : ℝ) * Real.log Y)) ≤
    ((SV.classFin A X d).card : ℝ)) with h𝒟def
  have h𝒟 : ∀ d ∈ 𝒟, d ∈ I ∧ (d : ℝ) ≤ Y ^ c ∧
      a * (X / ((d : ℝ) * Real.log Y)) ≤ ((SV.classFin A X d).card : ℝ) := by
    intro d hd
    rw [h𝒟def, Finset.mem_filter, hI₁def, Finset.mem_filter] at hd
    exact ⟨hd.1.1, hd.1.2, hd.2⟩
  -- the class sizes are bounded above
  have hup : ∀ d ∈ 𝒟, ((SV.classFin A X d).card : ℝ) ≤ c₂ * (X / ((d : ℝ) * Real.log Y)) := by
    intro d hd
    obtain ⟨hdI, hdc, _⟩ := h𝒟 d hd
    have h1 : (SV.classFin A X d).card ≤ cnt {n : ℕ | SV.smoothPart Y n = d} X :=
      card_filter_le_cnt hA (fun M => SV.smoothPart Y M = d)
    have h2 := (hXs X hX3 d (Nat.one_le_iff_ne_zero.2 (hI d hdI).1) (hI d hdI).2 hdc).2
    exact (Nat.cast_le.2 h1).trans h2
  refine ⟨𝒟, fun d hd => ?_, ⟨fun d hd => ⟨(h𝒟 d hd).2.2, hup d hd⟩, ?_⟩, ?_⟩
  · obtain ⟨hdI, hdc, _⟩ := h𝒟 d hd
    exact ⟨Nat.one_le_iff_ne_zero.2 (hI d hdI).1, (hI d hdI).2, hdc⟩
  · -- the reciprocal sum over `𝒟`
    -- (a) `#A = ∑_{d ∈ I} #𝒜_d`
    have hsplit : (A.card : ℝ) = ∑ d ∈ I, ((SV.classFin A X d).card : ℝ) := by
      rw [Finset.card_eq_sum_card_image (SV.smoothPart Y) A]
      push_cast
      rfl
    have hs1 := Finset.sum_filter_add_sum_filter_not I (fun d : ℕ => (d : ℝ) ≤ Y ^ c)
      (fun d : ℕ => ((SV.classFin A X d).card : ℝ))
    have hs2 := Finset.sum_filter_add_sum_filter_not I₁
      (fun d : ℕ => a * (X / ((d : ℝ) * Real.log Y)) ≤ ((SV.classFin A X d).card : ℝ))
      (fun d : ℕ => ((SV.classFin A X d).card : ℝ))
    -- (b) the classes with `d > Y^c` hold at most `cF X / 3` members
    have hbig : ∑ d ∈ I.filter (fun d : ℕ => ¬ (d : ℝ) ≤ Y ^ c), ((SV.classFin A X d).card : ℝ) ≤
        cF / 3 * X := by
      set s := A.filter (fun M => Y ^ c < (SV.smoothPart Y M : ℝ)) with hsdef
      have hmaps : (s : Set ℕ).MapsTo (SV.smoothPart Y) (I.filter (fun d : ℕ => ¬ (d : ℝ) ≤ Y ^ c)) := by
        intro M hM
        rw [Finset.mem_coe, hsdef, Finset.mem_filter] at hM
        rw [Finset.mem_coe, Finset.mem_filter]
        exact ⟨Finset.mem_image_of_mem _ hM.1, not_le.2 hM.2⟩
      have hfib := Finset.card_eq_sum_card_fiberwise hmaps
      have hfib' : ∑ d ∈ I.filter (fun d : ℕ => ¬ (d : ℝ) ≤ Y ^ c), ((SV.classFin A X d).card : ℝ) =
          (s.card : ℝ) := by
        rw [hfib]
        push_cast
        refine Finset.sum_congr rfl (fun d hd => ?_)
        rw [Finset.mem_filter] at hd
        congr 2
        ext M
        rw [SV.classFin, Finset.mem_filter, hsdef, Finset.mem_filter, Finset.mem_filter]
        constructor
        · rintro ⟨hM, hMd⟩
          refine ⟨⟨hM, ?_⟩, hMd⟩
          rw [hMd]
          exact not_le.1 hd.2
        · rintro ⟨⟨hM, _⟩, hMd⟩
          exact ⟨hM, hMd⟩
      rw [hfib']
      have h1 : s.card ≤ cnt {n : ℕ | Y ^ c < (SV.smoothPart Y n : ℝ)} X :=
        card_filter_le_cnt hA (fun M => Y ^ c < (SV.smoothPart Y M : ℝ))
      exact (Nat.cast_le.2 h1).trans (hXt X hX2)
    -- (c) the small classes with `d ≤ Y^c` outside `𝒟` hold at most `cF X / 3` members
    have hsmall : ∑ d ∈ I₁.filter (fun d : ℕ => ¬ a * (X / ((d : ℝ) * Real.log Y)) ≤
        ((SV.classFin A X d).card : ℝ)), ((SV.classFin A X d).card : ℝ) ≤ cF / 3 * X := by
      have h1 : ∑ d ∈ I₁.filter (fun d : ℕ => ¬ a * (X / ((d : ℝ) * Real.log Y)) ≤
          ((SV.classFin A X d).card : ℝ)), ((SV.classFin A X d).card : ℝ) ≤
          ∑ d ∈ I₁, a * X / Real.log Y * (1 / (d : ℝ)) := by
        refine (Finset.sum_le_sum (fun d hd => ?_)).trans
          (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun d _ _ => by positivity))
        rw [Finset.mem_filter] at hd
        have := (not_le.1 hd.2).le
        have e : a * (X / ((d : ℝ) * Real.log Y)) = a * X / Real.log Y * (1 / (d : ℝ)) := by
          field_simp
        rw [← e]
        exact this
      have h2 : ∑ d ∈ I₁, (1 : ℝ) / d ≤ (Delta Y)⁻¹ :=
        sum_inv_smooth_le Y I₁ (fun d hd => hI d (Finset.mem_filter.1 hd).1)
      have hΔ : 0 < Delta Y := by
        have : 0 < Delta Y * Real.log Y := lt_of_lt_of_le ha₀ hMY
        exact pos_of_mul_pos_left this hlY.le
      have h3 : (Delta Y)⁻¹ ≤ Real.log Y / a₀ := by
        rw [inv_eq_one_div, div_le_div_iff₀ hΔ ha₀, one_mul]
        linarith
      rw [← Finset.mul_sum] at h1
      have h4 : a * X / Real.log Y * ∑ d ∈ I₁, (1 : ℝ) / d ≤ a * X / Real.log Y * (Real.log Y / a₀) :=
        mul_le_mul_of_nonneg_left (h2.trans h3) (by positivity)
      have e : a * X / Real.log Y * (Real.log Y / a₀) = cF / 3 * X := by
        rw [hadef]
        field_simp
      linarith
    -- (d) conclusion
    have hD1 : cF / 3 * X ≤ ∑ d ∈ 𝒟, ((SV.classFin A X d).card : ℝ) := by
      have hc' : cF * X ≤ (A.card : ℝ) := hcard
      rw [h𝒟def]
      linarith
    have hD2 : ∑ d ∈ 𝒟, ((SV.classFin A X d).card : ℝ) ≤
        c₂ * X / Real.log Y * ∑ d ∈ 𝒟, (1 : ℝ) / d := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum (fun d hd => (hup d hd).trans (le_of_eq ?_))
      field_simp
    have h5 : cF / 3 * X ≤ c₂ * X / Real.log Y * ∑ d ∈ 𝒟, (1 : ℝ) / d := hD1.trans hD2
    have e : cF / (3 * c₂) * Real.log Y = (cF / 3 * X) / (c₂ * X / Real.log Y) := by
      field_simp
    rw [e, div_le_iff₀ (by positivity)]
    exact h5.trans (le_of_eq (mul_comm _ _))
  · -- disjointness of the images
    intro d hd d' hd' hne
    rw [Finset.disjoint_left]
    intro u hu hu'
    obtain ⟨M, hM, rfl⟩ := Finset.mem_image.1 hu
    obtain ⟨M', hM', hMM'⟩ := Finset.mem_image.1 hu'
    rw [SV.classFin, Finset.mem_filter] at hM hM'
    apply hne
    rw [← hM.2, ← hM'.2, ← hsa M hM.1, ← hsa M' hM'.1, hMM']

end Principia.Erdos1054.Proofs

namespace Principia.Erdos1054.Proofs.SvRegular

open Finset Filter Principia.Erdos1054

/-! ## The Luca–Pomerance level `y(u) = log log u / log log log u` -/

theorem yOf_eq (u : ℝ) :
    SV.yOf u = Real.log (Real.log u) / Real.log (Real.log (Real.log u)) := rfl

theorem yLP_eq_yOf (n : ℕ) : yLP n = SV.yOf (n : ℝ) := rfl

theorem log_sub_log_le {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Real.log x - Real.log y ≤ (x - y) / y := by
  rw [← Real.log_div hx.ne' hy.ne']
  have := Real.log_le_sub_one_of_pos (div_pos hx hy)
  have e : x / y - 1 = (x - y) / y := by field_simp
  linarith

/-- The threshold `e^{e^e}` above which `y` is increasing. -/
noncomputable def uThr : ℝ := Real.exp (Real.exp (Real.exp 1))

theorem uThr_pos : 0 < uThr := Real.exp_pos _

theorem loglog_ge_e {u : ℝ} (hu : uThr ≤ u) : Real.exp 1 ≤ Real.log (Real.log u) := by
  have h1 : Real.exp (Real.exp 1) ≤ Real.log u := by
    have := Real.log_le_log uThr_pos hu
    have e : Real.log uThr = Real.exp (Real.exp 1) := Real.log_exp _
    rwa [e] at this
  have := Real.log_le_log (Real.exp_pos _) h1
  rwa [Real.log_exp] at this

/-- `L ↦ L / log L` is increasing on `[e, ∞)`. -/
theorem div_log_mono {a b : ℝ} (ha : Real.exp 1 ≤ a) (hab : a ≤ b) :
    a / Real.log a ≤ b / Real.log b := by
  have ha0 : 0 < a := lt_of_lt_of_le (Real.exp_pos 1) ha
  have hb0 : 0 < b := by linarith
  have hla : 1 ≤ Real.log a := by
    have := Real.log_le_log (Real.exp_pos 1) ha
    rwa [Real.log_exp] at this
  have hlb : Real.log a ≤ Real.log b := Real.log_le_log ha0 hab
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  have h1 := log_sub_log_le hb0 ha0
  -- a log b ≤ a log a + (b − a) ≤ a log a + (b − a) log a = b log a
  have h2 : a * (Real.log b - Real.log a) ≤ b - a := by
    have := mul_le_mul_of_nonneg_left h1 ha0.le
    have e : a * ((b - a) / a) = b - a := by field_simp
    linarith
  have h3 : b - a ≤ (b - a) * Real.log a := le_mul_of_one_le_right (by linarith) hla
  nlinarith

/-- `y` is increasing on `[e^{e^e}, ∞)`. -/
theorem yOf_mono {u v : ℝ} (hu : uThr ≤ u) (huv : u ≤ v) : SV.yOf u ≤ SV.yOf v := by
  have ha := loglog_ge_e hu
  have hu0 : 0 < u := lt_of_lt_of_le uThr_pos hu
  have hlu : 0 < Real.log u := by
    have := lt_of_lt_of_le (Real.exp_pos 1) ha
    by_contra h
    push Not at h
    have h' : Real.log (Real.log u) ≤ 0 := by
      rcases h.lt_or_eq with h | h
      · -- `log u < 0`: then `log (log u) = log |log u|`, and `|log u| < 1` or not; use `u ≥ 1`
        have hu1 : 1 ≤ u := le_trans (by
          have : (1 : ℝ) ≤ uThr := Real.one_le_exp (Real.exp_pos _).le
          exact this) hu
        have := Real.log_nonneg hu1
        linarith
      · rw [h, Real.log_zero]
    linarith
  have hab : Real.log (Real.log u) ≤ Real.log (Real.log v) :=
    Real.log_le_log hlu (Real.log_le_log hu0 huv)
  rw [yOf_eq, yOf_eq]
  exact div_log_mono ha hab

/-- For `u ≥ e^{e^e}`: `0 ≤ y(u) ≤ log log u`. -/
theorem yOf_le_loglog {u : ℝ} (hu : uThr ≤ u) :
    0 ≤ SV.yOf u ∧ SV.yOf u ≤ Real.log (Real.log u) := by
  have ha := loglog_ge_e hu
  have ha0 : 0 < Real.log (Real.log u) := lt_of_lt_of_le (Real.exp_pos 1) ha
  have hla : 1 ≤ Real.log (Real.log (Real.log u)) := by
    have := Real.log_le_log (Real.exp_pos 1) ha
    rwa [Real.log_exp] at this
  rw [yOf_eq]
  exact ⟨div_nonneg ha0.le (by linarith), div_le_self ha0.le hla⟩

/-- For large `X`: `y(X) < X^{1/15}`. -/
theorem eventually_yOf_lt : ∃ X₀ : ℝ, ∀ X ≥ X₀, SV.yOf X < X ^ ((1 : ℝ) / 15) := by
  obtain ⟨X₁, hX₁⟩ := eventually_atTop.1
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 30)).eventually_gt_atTop 30)
  refine ⟨max X₁ uThr, fun X hX => ?_⟩
  have hXu : uThr ≤ X := le_trans (le_max_right _ _) hX
  have hX0 : 0 < X := lt_of_lt_of_le uThr_pos hXu
  have h30 : 30 < X ^ ((1 : ℝ) / 30) := hX₁ X (le_trans (le_max_left _ _) hX)
  have hy := (yOf_le_loglog hXu).2
  have hl1 : Real.log (Real.log X) ≤ Real.log X - 1 := by
    have hlX : 0 < Real.log X := by
      have := loglog_ge_e hXu
      by_contra h
      push Not at h
      have h1 : (1 : ℝ) ≤ X := le_trans (Real.one_le_exp (Real.exp_pos _).le) hXu
      have h2 := Real.log_nonneg h1
      have h3 : Real.log X = 0 := le_antisymm h h2
      rw [h3, Real.log_zero] at this
      linarith [Real.exp_pos 1]
    exact Real.log_le_sub_one_of_pos hlX
  have hl2 : Real.log X ≤ X ^ ((1 : ℝ) / 30) / (1 / 30) :=
    Real.log_le_rpow_div hX0.le (by norm_num)
  have hsq : X ^ ((1 : ℝ) / 15) = X ^ ((1 : ℝ) / 30) * X ^ ((1 : ℝ) / 30) := by
    rw [← Real.rpow_add hX0]
    norm_num
  rw [hsq]
  have : X ^ ((1 : ℝ) / 30) / (1 / 30) = 30 * X ^ ((1 : ℝ) / 30) := by ring
  nlinarith

/-- `Y = y(X^{1/120})` versus `y(X)`: the reciprocal prime sum over `(Y, y(X)]` tends to zero
(EP1054.tex line 1428), from Mertens' second theorem. -/
theorem mid_small (h2 : Principia.Erdos1054.Std_Mertens2) (ε : ℝ) (hε : 0 < ε) :
    ∃ X₀ : ℝ, ∀ X ≥ X₀, ∑ p ∈ SV.primesIoc (SV.Ycut X) (SV.yOf X), (1 : ℝ) / p ≤ ε := by
  obtain ⟨M, C, hM⟩ := h2
  obtain ⟨X₁, hX₁⟩ := eventually_atTop.1 (tendsto_Ycut.eventually_ge_atTop
    (max 2 (Real.exp ((1 + 2 * |C|) / ε))))
  obtain ⟨X₂, hX₂⟩ := eventually_atTop.1 (tendsto_loglog_rpow.eventually_ge_atTop
    (max (Real.log 120) 2))
  obtain ⟨X₃, hX₃⟩ := eventually_atTop.1 (Real.tendsto_log_atTop.eventually_gt_atTop (0 : ℝ))
  refine ⟨max (max X₁ X₂) (max X₃ 1), fun X hX => ?_⟩
  have hXa := hX₁ X (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hX))
  have hXb := hX₂ X (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hX))
  have hlX : 0 < Real.log X := hX₃ X (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hX))
  have hX1 : 1 ≤ X := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hX)
  have hX0 : 0 < X := by linarith
  set a := SV.Ycut X with hadef
  set b := SV.yOf X with hbdef
  have ha2 : 2 ≤ a := le_trans (le_max_left _ _) hXa
  have hla : (1 + 2 * |C|) / ε ≤ Real.log a := by
    have h := le_trans (le_max_right _ _) hXa
    have := Real.log_le_log (Real.exp_pos _) h
    rwa [Real.log_exp] at this
  have hla0 : 0 < Real.log a := Real.log_pos (by linarith)
  by_cases hab : a ≤ b
  swap
  · push Not at hab
    have : SV.primesIoc a b = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro p hp
      simp only [SV.primesIoc, Finset.mem_filter, Finset.mem_Iic] at hp
      have hb' : 0 ≤ b := by
        by_contra hneg
        push Not at hneg
        have h0 := Nat.floor_eq_zero.2 (by linarith : b < 1)
        have := hp.2.1.two_le
        omega
      have h1 : (p : ℝ) ≤ b := (Nat.cast_le.2 hp.1).trans (Nat.floor_le hb')
      linarith [hp.2.2]
    rw [this, Finset.sum_empty]
    exact hε.le
  -- `L' = log log X^{1/120} = L − log 120`
  set L := Real.log (Real.log X) with hLdef
  set L' := Real.log (Real.log (X ^ ((1 : ℝ) / 120))) with hL'def
  have hL'L : L' = L - Real.log 120 := by
    rw [hL'def, Real.log_rpow hX0, show (1 : ℝ) / 120 * Real.log X = Real.log X / 120 by ring,
      Real.log_div hlX.ne' (by norm_num)]
  have hL'2 : 2 ≤ L' := le_trans (le_max_right _ _) hXb
  have hL'120 : Real.log 120 ≤ L' := le_trans (le_max_left _ _) hXb
  have hL'0 : 0 < L' := by linarith
  have hL0 : 0 < L := by
    have : 0 < Real.log 120 := Real.log_pos (by norm_num)
    linarith
  have hlL' : 0 < Real.log L' := Real.log_pos (by linarith)
  have hlL'L : Real.log L' ≤ Real.log L := Real.log_le_log hL'0 (by
    have : 0 < Real.log 120 := Real.log_pos (by norm_num)
    linarith)
  have hb0 : 0 < b := by linarith
  -- `b ≤ a (L/L')`
  have hbL : b ≤ L / Real.log L' := by
    rw [hbdef, yOf_eq]
    exact div_le_div_of_nonneg_left hL0.le hlL' hlL'L
  have ha_eq : a = L' / Real.log L' := rfl
  have haL : L / Real.log L' = a * (L / L') := by
    rw [ha_eq]
    field_simp
  have hlogb : Real.log b ≤ Real.log a + Real.log 120 / L' := by
    have h1 : Real.log b ≤ Real.log (a * (L / L')) :=
      Real.log_le_log hb0 (hbL.trans (le_of_eq haL))
    rw [Real.log_mul (by linarith) (by positivity)] at h1
    have h2 := Real.log_le_sub_one_of_pos (show 0 < L / L' by positivity)
    have e : L / L' - 1 = Real.log 120 / L' := by
      rw [div_sub_one hL'0.ne']
      congr 1
      linarith
    linarith
  have hlb0 : 0 < Real.log b := Real.log_pos (by linarith)
  have hlab : Real.log a ≤ Real.log b := Real.log_le_log (by linarith) hab
  have hll : Real.log (Real.log b) - Real.log (Real.log a) ≤ (Real.log 120 / L') / Real.log a := by
    have := log_sub_log_le hlb0 hla0
    have h2 : (Real.log b - Real.log a) / Real.log a ≤ (Real.log 120 / L') / Real.log a :=
      div_le_div_of_nonneg_right (by linarith) hla0.le
    linarith
  have h120 : Real.log 120 / L' ≤ 1 := by rw [div_le_one hL'0]; exact hL'120
  have hsplit := sum_primes_split (by linarith : (0 : ℝ) ≤ a) hab
  have hMb := (abs_le.1 (hM b (by linarith))).2
  have hMa := (abs_le.1 (hM a ha2)).1
  have hCb : C / Real.log b ≤ |C| / Real.log a :=
    (div_le_div_of_nonneg_right (le_abs_self C) hlb0.le).trans
      (div_le_div_of_nonneg_left (abs_nonneg C) hla0 hlab)
  have hCa : C / Real.log a ≤ |C| / Real.log a := div_le_div_of_nonneg_right (le_abs_self C) hla0.le
  have hfin : (Real.log 120 / L') / Real.log a + 2 * (|C| / Real.log a) ≤ ε := by
    have e : (Real.log 120 / L') / Real.log a + 2 * (|C| / Real.log a) =
        (Real.log 120 / L' + 2 * |C|) / Real.log a := by field_simp
    rw [e, div_le_iff₀ hla0]
    have := mul_le_mul_of_nonneg_left hla hε.le
    have e2 : ε * ((1 + 2 * |C|) / ε) = 1 + 2 * |C| := by field_simp
    linarith
  linarith

/-! ## The regularity properties at one level `t` -/

theorem isRough_mul {y : ℝ} {a b : ℕ} (ha : IsRough y a) (hb : IsRough y b) :
    IsRough y (a * b) := by
  intro p hp
  have hp' := Nat.mem_primeFactors.1 hp
  have hab : a ≠ 0 ∧ b ≠ 0 := by
    constructor
    · rintro rfl; simp at hp'
    · rintro rfl; simp at hp'
  rcases (Nat.Prime.dvd_mul hp'.1).1 hp'.2.1 with h | h
  · exact ha p (Nat.mem_primeFactors.2 ⟨hp'.1, h, hab.1⟩)
  · exact hb p (Nat.mem_primeFactors.2 ⟨hp'.1, h, hab.2⟩)

theorem isRough_prime {y : ℝ} {p : ℕ} (hp : p.Prime) (h : y < p) : IsRough y p := by
  intro q hq
  rw [Nat.Prime.primeFactors hp, Finset.mem_singleton] at hq
  rw [hq]
  exact h

/-- `D_y(t w) = D_y(t)` for `y`-rough `w`. -/
theorem smoothPart_mul_rough_right {y : ℝ} {t w : ℕ} (ht : t ≠ 0) (hw0 : w ≠ 0)
    (hw : IsRough y w) : SV.smoothPart y (t * w) = SV.smoothPart y t := by
  obtain ⟨hmt, hms⟩ := smoothPart_spec (y := y) ht
  have hm0 : SV.smoothPart y t ≠ 0 := smoothPart_ne_zero ht
  have hu := isRough_div_smoothPart (y := y) ht
  have ht' : SV.smoothPart y t * (t / SV.smoothPart y t) = t := Nat.mul_div_cancel' hmt
  have hu0 : t / SV.smoothPart y t ≠ 0 := by
    intro h
    rw [h, mul_zero] at ht'
    exact ht ht'.symm
  have e : t * w = SV.smoothPart y t * (t / SV.smoothPart y t * w) := by
    rw [← mul_assoc, ht']
  rw [e]
  exact smoothPart_mul_rough hm0 (mul_ne_zero hu0 hw0) hms (isRough_mul hu hw)

theorem le_sig {t : ℕ} (ht : t ≠ 0) : t ≤ sig t := by
  show t ≤ ArithmeticFunction.sigma 1 t
  rw [ArithmeticFunction.sigma_one_apply]
  exact Finset.single_le_sum (f := fun d => d) (fun _ _ => Nat.zero_le _)
    (Nat.mem_divisors_self t ht)

/-- The Luca–Pomerance conclusions at a level `t`, together with `Y ≤ y(t)` and the absence of
prime factors of `t` in `(Y, y(t)]`, give the properties (i)–(ii) of `lem:sv-regular` at `t`
(EP1054.tex lines 1460–1465). -/
theorem regularAt_of {Y : ℝ} {t M : ℕ} (ht0 : t ≠ 0) (hs0 : aliquot t ≠ 0)
    (h1 : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ yLP t → t.factorization p < (sig t).factorization p)
    (h2 : IsSmooth (yLP t) (Nat.gcd t (sig t)))
    (h3 : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ yLP t → p ∣ sig t / Nat.gcd t (sig t))
    (h4 : IsRough (yLP t) (aliquot t / Nat.gcd t (sig t)))
    (hY : Y ≤ yLP t)
    (hmid : ∀ p ∈ t.primeFactors, ¬ (Y < p ∧ (p : ℝ) ≤ yLP t))
    (hDM : SV.smoothPart Y M = SV.smoothPart Y t) :
    SV.RegularAt Y (SV.smoothPart Y M) t := by
  have hs0' : sig t - t ≠ 0 := hs0
  have hsig0 : sig t ≠ 0 := by omega
  have hg0 : Nat.gcd t (sig t) ≠ 0 := Nat.gcd_ne_zero_left ht0
  have hgt : Nat.gcd t (sig t) ∣ t := Nat.gcd_dvd_left _ _
  have hgs : Nat.gcd t (sig t) ∣ sig t := Nat.gcd_dvd_right _ _
  have hgY : IsSmooth Y (Nat.gcd t (sig t)) := by
    intro p hp
    have hp2 := h2 p hp
    have hpt : p ∈ t.primeFactors := Nat.primeFactors_mono hgt ht0 hp
    by_contra hlt
    push Not at hlt
    exact hmid p hpt ⟨hlt, hp2⟩
  obtain ⟨hmt, hms⟩ := smoothPart_spec (y := Y) ht0
  have hm0 : SV.smoothPart Y t ≠ 0 := smoothPart_ne_zero ht0
  have hms' : SV.smoothPart Y t ∣ sig t := by
    rw [← Nat.factorization_le_iff_dvd hm0 hsig0]
    intro p
    by_cases hp : p ∈ (SV.smoothPart Y t).primeFactors
    · have hpp := (Nat.mem_primeFactors.1 hp).1
      have hpY := hms p hp
      have h5 := h1 p hpp (hpY.trans hY)
      have hle : (SV.smoothPart Y t).factorization p ≤ t.factorization p :=
        (Nat.factorization_le_iff_dvd hm0 ht0).2 hmt p
      exact hle.trans h5.le
    · have : (SV.smoothPart Y t).factorization p = 0 := by
        rw [← Finsupp.notMem_support_iff, Nat.support_factorization]
        exact hp
      rw [this]
      exact Nat.zero_le _
  have hmg : SV.smoothPart Y t ∣ Nat.gcd t (sig t) := Nat.dvd_gcd hmt hms'
  have hgm : Nat.gcd t (sig t) ∣ SV.smoothPart Y t := dvd_smoothPart ht0 hgt hgY
  have hgm_eq : Nat.gcd t (sig t) = SV.smoothPart Y t := Nat.dvd_antisymm hgm hmg
  have hgs' : Nat.gcd t (sig t) ∣ aliquot t := Nat.dvd_sub hgs hgt
  have hapos : 0 < aliquot t := Nat.pos_of_ne_zero hs0
  have hw0 : aliquot t / Nat.gcd t (sig t) ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd hapos hgs') (Nat.pos_of_ne_zero hg0)).ne'
  have hwY : IsRough Y (aliquot t / Nat.gcd t (sig t)) := fun p hp => lt_of_le_of_lt hY (h4 p hp)
  have hsa : SV.smoothPart Y (aliquot t) = Nat.gcd t (sig t) := by
    have e : aliquot t = Nat.gcd t (sig t) * (aliquot t / Nat.gcd t (sig t)) :=
      (Nat.mul_div_cancel' hgs').symm
    rw [e]
    exact smoothPart_mul_rough hg0 hw0 hgY hwY
  rw [hDM]
  refine ⟨hgm_eq.symm, rfl, by rw [hsa, hgm_eq], fun p hp hpY => ?_, ?_⟩
  · rw [← hgm_eq]
    exact h3 p hp (hpY.trans hY)
  · rw [← hgm_eq]
    exact h4

/-- `eq:sv-LP25` at the threshold `(log log X)^2` from LP Lemma 2.5 at `(log log n)^2`, `n ≤ X`. -/
theorem lp25_transfer {X : ℝ} {n : ℕ} (hn3 : 3 ≤ n) (hnX : (n : ℝ) ≤ X)
    (h : ∑ r ∈ (sig n).primeFactors.filter (fun r : ℕ => (logIt 2 (n : ℝ)) ^ 2 < (r : ℝ)),
      (1 : ℝ) / r ≤ 1) : Eq_SvLP25 X n := by
  unfold Eq_SvLP25
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)) h
  intro r hr
  rw [Finset.mem_filter] at hr ⊢
  refine ⟨hr.1, lt_of_le_of_lt ?_ hr.2⟩
  have hn3' : (3 : ℝ) ≤ n := by exact_mod_cast hn3
  have hn0 : (0 : ℝ) < n := by linarith
  have hln : 1 ≤ Real.log n := by
    have h1 : Real.exp 1 ≤ n := by
      have := Real.exp_one_lt_d9
      linarith
    have := Real.log_le_log (Real.exp_pos 1) h1
    rwa [Real.log_exp] at this
  have hll0 : 0 ≤ Real.log (Real.log n) := Real.log_nonneg hln
  have hll : Real.log (Real.log n) ≤ Real.log (Real.log X) :=
    Real.log_le_log (by linarith) (Real.log_le_log hn0 hnX)
  show (Real.log (Real.log n)) ^ 2 ≤ (Real.log (Real.log X)) ^ 2
  exact pow_le_pow_left₀ hll0 hll 2

/-- `eq:sv-image-abundancy` from Pollack's exclusion and `s(n)/n < C_δ` (EP1054.tex
lines 1470–1479), with `B_δ = C_δ + 2`. -/
theorem imageAbundancy_of {n : ℕ} {Cδ : ℝ} (hs0 : aliquot n ≠ 0)
    (hlt : (aliquot n : ℝ) / n < Cδ)
    (hP : ¬ ((aliquot n : ℝ) / n + 1 < (aliquot (aliquot n) : ℝ) / (aliquot n : ℝ))) :
    Eq_SvImageAbundancy (Cδ + 2) n := by
  unfold Eq_SvImageAbundancy abundancy
  push Not at hP
  set m := aliquot n with hm
  have hm0 : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hs0
  have hsig : (sig m : ℝ) = (aliquot m : ℝ) + m := by
    have := le_sig hs0
    show ((sig m : ℕ) : ℝ) = ((sig m - m : ℕ) : ℝ) + m
    rw [Nat.cast_sub this]
    ring
  rw [hsig, add_div, div_self hm0.ne']
  linarith

/-! ## Counting the members of `𝒜₀(X)` with a prescribed `(q, r, k)`-property -/

/-- Chebyshev: `π(x) ≤ 8 x / log x` for `x > 1`. -/
theorem card_primesLE_le {x : ℝ} (hx : 1 < x) :
    ((Nat.primesLE ⌊x⌋₊).card : ℝ) ≤ 8 * x / Real.log x := by
  rw [Nat.primesLE_card_eq_primeCounting]
  have h := Chebyshev.pi_le_log4_mul_div hx
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos hx
  rw [Real.log_sqrt hx0.le] at h
  have hl4 : Real.log 4 ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    linarith
  have hsq : Real.sqrt x * Real.log x ≤ 2 * x := by
    have h1 := Real.log_le_rpow_div hx0.le (by norm_num : (0 : ℝ) < 1 / 2)
    rw [← Real.sqrt_eq_rpow] at h1
    have h2 : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
    have h3 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
    have h4 : Real.sqrt x * Real.log x ≤ Real.sqrt x * (Real.sqrt x / (1 / 2)) :=
      mul_le_mul_of_nonneg_left h1 h3
    have e : Real.sqrt x * (Real.sqrt x / (1 / 2)) = 2 * (Real.sqrt x * Real.sqrt x) := by ring
    rw [h2] at e
    linarith
  have hsq' : Real.sqrt x ≤ 2 * x / Real.log x := by rw [le_div_iff₀ hlx]; exact hsq
  have h5 : Real.log 4 * x / (Real.log x / 2) ≤ 6 * x / Real.log x := by
    rw [div_le_div_iff₀ (by positivity) hlx]
    have : Real.log 4 * x * Real.log x ≤ 3 * x * Real.log x := by
      have := mul_le_mul_of_nonneg_right hl4 (by positivity : (0 : ℝ) ≤ x * Real.log x)
      linarith
    nlinarith
  have e : 8 * x / Real.log x = 6 * x / Real.log x + 2 * x / Real.log x := by ring
  linarith

/-- The `q`-range of `eq:sv-factorization`. -/
noncomputable def Qset (X : ℝ) : Finset ℕ := SV.primesIoc (X ^ ((7 : ℝ) / 20)) (X ^ ((11 : ℝ) / 30))

/-- The `r`-range of `eq:sv-factorization`. -/
noncomputable def Rset (X : ℝ) : Finset ℕ := SV.primesIoc (X ^ ((1 : ℝ) / 15)) (X ^ ((1 : ℝ) / 12))

/-- The `k`-range of `eq:sv-factorization` (the conditions `D ∣ k`, `σ(j)/j ≤ 4ζ(2)` dropped). -/
noncomputable def Kset (X : ℝ) : Finset ℕ :=
  (Finset.Icc 1 ⌊X ^ ((1 : ℝ) / 60)⌋₊).filter (fun k : ℕ => X ^ ((1 : ℝ) / 120) < (k : ℝ))

theorem mem_primesIoc {a b : ℝ} {p : ℕ} :
    p ∈ SV.primesIoc a b ↔ p ≤ ⌊b⌋₊ ∧ p.Prime ∧ a < (p : ℝ) := by
  rw [SV.primesIoc, Finset.mem_filter, Finset.mem_Iic]

theorem tuple_mem {D p q r k : ℕ} {X : ℝ} (hX : 0 ≤ X) (h : S4a.A0Tuple D X p q r k) :
    q ∈ Qset X ∧ r ∈ Rset X ∧ k ∈ Kset X := by
  obtain ⟨_, hq, hr, _, hk1, hk2, hr1, hr2, hq1, hq2, _, _⟩ := h
  refine ⟨mem_primesIoc.2 ⟨Nat.le_floor hq2, hq, hq1⟩, mem_primesIoc.2 ⟨Nat.le_floor hr2, hr, hr1⟩,
    ?_⟩
  rw [Kset, Finset.mem_filter, Finset.mem_Icc]
  refine ⟨⟨?_, Nat.le_floor hk2⟩, hk1⟩
  have : (0 : ℝ) < k := lt_of_le_of_lt (Real.rpow_nonneg hX _) hk1
  exact_mod_cast this

open Classical in
/-- The members of `𝒜₀(X)` having a tuple with a property `Φ(q, r, k)` number at most
`∑_{(q, r, k) with Φ} π(X/(qrk))`. -/
theorem card_tuples_le (D : ℕ) {X : ℝ} (hX : 0 ≤ X) (Φ : ℕ → ℕ → ℕ → Prop) :
    ((S4a.A0 D X).filter (fun M => ∃ p q r k : ℕ, S4a.A0Tuple D X p q r k ∧
        M = p * q * r * k ∧ Φ q r k)).card ≤
      ∑ τ ∈ (Qset X ×ˢ (Rset X ×ˢ Kset X)).filter (fun τ => Φ τ.1 τ.2.1 τ.2.2),
        (Nat.primesLE ⌊X / ((τ.1 : ℝ) * τ.2.1 * τ.2.2)⌋₊).card := by
  refine le_trans (Finset.card_le_card (t := ((Qset X ×ˢ (Rset X ×ˢ Kset X)).filter
      (fun τ => Φ τ.1 τ.2.1 τ.2.2)).biUnion
        (fun τ => (Nat.primesLE ⌊X / ((τ.1 : ℝ) * τ.2.1 * τ.2.2)⌋₊).image
          (fun p => p * τ.1 * τ.2.1 * τ.2.2))) ?_)
    (Finset.card_biUnion_le.trans (Finset.sum_le_sum (fun τ _ => Finset.card_image_le)))
  intro M hM
  rw [Finset.mem_filter] at hM
  obtain ⟨p, q, r, k, ht, rfl, hΦ⟩ := hM.2
  rw [Finset.mem_biUnion]
  obtain ⟨hqQ, hrR, hkK⟩ := tuple_mem hX ht
  obtain ⟨hpp, -, -, -, -, -, -, -, -, -, -, hpX⟩ := ht
  refine ⟨(q, r, k), Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hqQ,
    Finset.mem_product.2 ⟨hrR, hkK⟩⟩, hΦ⟩, Finset.mem_image.2 ⟨p, ?_, rfl⟩⟩
  rw [Nat.mem_primesLE]
  exact ⟨Nat.le_floor hpX, hpp⟩

theorem sum_prod3 (A B C : Finset ℕ) (f g h : ℕ → ℝ) :
    ∑ τ ∈ A ×ˢ (B ×ˢ C), f τ.1 * (g τ.2.1 * h τ.2.2) =
      (∑ a ∈ A, f a) * ((∑ b ∈ B, g b) * (∑ c ∈ C, h c)) := by
  rw [Finset.sum_product, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.sum_product, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Finset.mul_sum]

theorem sum_prod2 (A : Finset ℕ) (S : Finset (ℕ × ℕ)) (f : ℕ → ℝ) (G : ℕ × ℕ → ℝ) :
    ∑ τ ∈ A ×ˢ S, f τ.1 * G τ.2 = (∑ a ∈ A, f a) * (∑ σ ∈ S, G σ) := by
  rw [Finset.sum_product, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.mul_sum]

/-- Reciprocal sum over integers `≤ N` divisible by some prime of a finite set `L`. -/
theorem sum_inv_multiples_le (L : Finset ℕ) (hL : ∀ ℓ ∈ L, 1 ≤ ℓ) (N : ℕ) (S : Finset ℕ)
    (hS : ∀ k ∈ S, 1 ≤ k ∧ k ≤ N ∧ ∃ ℓ ∈ L, ℓ ∣ k) :
    ∑ k ∈ S, (1 : ℝ) / k ≤ (∑ ℓ ∈ L, (1 : ℝ) / ℓ) * ∑ j ∈ Finset.Icc 1 N, (1 : ℝ) / j := by
  have step1 : ∑ k ∈ S, (1 : ℝ) / k ≤
      ∑ k ∈ S, ∑ ℓ ∈ L, (if ℓ ∣ k then (1 : ℝ) / k else 0) := by
    apply Finset.sum_le_sum
    intro k hk
    obtain ⟨_, _, ℓ, hℓ, hdvd⟩ := hS k hk
    have := Finset.single_le_sum (f := fun ℓ => if ℓ ∣ k then (1 : ℝ) / k else 0)
      (fun i _ => by split_ifs <;> positivity) hℓ
    simp only [hdvd, if_true] at this
    exact this
  rw [Finset.sum_comm] at step1
  refine step1.trans ?_
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro ℓ hℓ
  have hℓ1 := hL ℓ hℓ
  have hℓ0 : 0 < ℓ := hℓ1
  rw [← Finset.sum_filter]
  -- the multiples of `ℓ` in `S` are `ℓ j` with `1 ≤ j ≤ N`
  have hsub : S.filter (fun k => ℓ ∣ k) ⊆ (Finset.Icc 1 N).image (fun j => ℓ * j) := by
    intro k hk
    rw [Finset.mem_filter] at hk
    obtain ⟨hk1, hkN, _⟩ := hS k hk.1
    obtain ⟨j, rfl⟩ := hk.2
    refine Finset.mem_image.2 ⟨j, Finset.mem_Icc.2 ⟨?_, ?_⟩, rfl⟩
    · rcases Nat.eq_zero_or_pos j with h | h
      · rw [h, mul_zero] at hk1
        omega
      · exact h
    · exact le_trans (Nat.le_mul_of_pos_left j hℓ0) hkN
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)).trans ?_
  rw [Finset.sum_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hℓ0 h), Finset.mul_sum]
  apply le_of_eq
  refine Finset.sum_congr rfl (fun j _ => ?_)
  push_cast
  rw [one_div_mul_one_div]

/-! ## The factor ranges -/

theorem q_facts {X : ℝ} (hX : 1 ≤ X) {q : ℕ} (hq : q ∈ Qset X) :
    q.Prime ∧ X ^ ((7 : ℝ) / 20) < q ∧ (q : ℝ) ≤ X ^ ((11 : ℝ) / 30) := by
  obtain ⟨hq1, hq2, hq3⟩ := mem_primesIoc.1 hq
  exact ⟨hq2, hq3, (Nat.cast_le.2 hq1).trans (Nat.floor_le (Real.rpow_nonneg (by linarith) _))⟩

theorem r_facts {X : ℝ} (hX : 1 ≤ X) {r : ℕ} (hr : r ∈ Rset X) :
    r.Prime ∧ X ^ ((1 : ℝ) / 15) < r ∧ (r : ℝ) ≤ X ^ ((1 : ℝ) / 12) := by
  obtain ⟨hr1, hr2, hr3⟩ := mem_primesIoc.1 hr
  exact ⟨hr2, hr3, (Nat.cast_le.2 hr1).trans (Nat.floor_le (Real.rpow_nonneg (by linarith) _))⟩

theorem k_facts {X : ℝ} (hX : 1 ≤ X) {k : ℕ} (hk : k ∈ Kset X) :
    1 ≤ k ∧ X ^ ((1 : ℝ) / 120) < k ∧ (k : ℝ) ≤ X ^ ((1 : ℝ) / 60) := by
  rw [Kset, Finset.mem_filter, Finset.mem_Icc] at hk
  exact ⟨hk.1.1, hk.2, (Nat.cast_le.2 hk.1.2).trans (Nat.floor_le (Real.rpow_nonneg (by linarith) _))⟩

theorem qrk_le {X : ℝ} (hX : 1 ≤ X) {q r k : ℕ} (hq : (q : ℝ) ≤ X ^ ((11 : ℝ) / 30))
    (hr : (r : ℝ) ≤ X ^ ((1 : ℝ) / 12)) (hk : (k : ℝ) ≤ X ^ ((1 : ℝ) / 60)) :
    (q : ℝ) * r * k ≤ X ^ ((7 : ℝ) / 15) := by
  have hX0 : 0 < X := by linarith
  have e : X ^ ((7 : ℝ) / 15) = X ^ ((11 : ℝ) / 30) * X ^ ((1 : ℝ) / 12) * X ^ ((1 : ℝ) / 60) := by
    rw [← Real.rpow_add hX0, ← Real.rpow_add hX0]
    norm_num
  rw [e]
  exact mul_le_mul (mul_le_mul hq hr (Nat.cast_nonneg _) (Real.rpow_nonneg hX0.le _)) hk
    (Nat.cast_nonneg _) (by positivity)

theorem rk_le {X : ℝ} (hX : 1 ≤ X) {r k : ℕ} (hr : (r : ℝ) ≤ X ^ ((1 : ℝ) / 12))
    (hk : (k : ℝ) ≤ X ^ ((1 : ℝ) / 60)) : (r : ℝ) * k ≤ X ^ ((1 : ℝ) / 10) := by
  have hX0 : 0 < X := by linarith
  have e : X ^ ((1 : ℝ) / 10) = X ^ ((1 : ℝ) / 12) * X ^ ((1 : ℝ) / 60) := by
    rw [← Real.rpow_add hX0]
    norm_num
  rw [e]
  exact mul_le_mul hr hk (Nat.cast_nonneg _) (Real.rpow_nonneg hX0.le _)

/-- `ℓ = r k` determines `(r, k)` on the ranges (EP1054.tex line 1449). -/
theorem rk_inj {X : ℝ} (hX : 1 ≤ X) {r k r' k' : ℕ} (hr : r ∈ Rset X) (hk' : k' ∈ Kset X)
    (hr' : r' ∈ Rset X) (h : r * k = r' * k') : r = r' ∧ k = k' := by
  obtain ⟨hrp, hr1, -⟩ := r_facts hX hr
  obtain ⟨hr'p, -, -⟩ := r_facts hX hr'
  obtain ⟨hk'1, -, hk'2⟩ := k_facts hX hk'
  have hdvd : r ∣ r' * k' := ⟨k, h.symm⟩
  rcases (Nat.Prime.dvd_mul hrp).1 hdvd with h1 | h1
  · have hrr : r = r' := (Nat.prime_dvd_prime_iff_eq hrp hr'p).1 h1
    subst hrr
    exact ⟨rfl, Nat.eq_of_mul_eq_mul_left hrp.pos h⟩
  · exfalso
    have h2 : r ≤ k' := Nat.le_of_dvd hk'1 h1
    have h3 : (r : ℝ) ≤ k' := by exact_mod_cast h2
    have h4 : X ^ ((1 : ℝ) / 60) ≤ X ^ ((1 : ℝ) / 15) :=
      Real.rpow_le_rpow_of_exponent_le hX (by norm_num)
    linarith

/-- `n = q r k` determines `(q, r, k)` on the ranges (EP1054.tex line 1449). -/
theorem qrk_inj {X : ℝ} (hX : 1 ≤ X) {q r k q' r' k' : ℕ} (hq : q ∈ Qset X) (hr : r ∈ Rset X)
    (hq' : q' ∈ Qset X) (hr' : r' ∈ Rset X) (hk' : k' ∈ Kset X) (h : q * r * k = q' * r' * k') :
    q = q' ∧ r = r' ∧ k = k' := by
  obtain ⟨hqp, hq1, -⟩ := q_facts hX hq
  obtain ⟨hq'p, -, -⟩ := q_facts hX hq'
  obtain ⟨-, -, hr'2⟩ := r_facts hX hr'
  obtain ⟨hk'1, -, hk'2⟩ := k_facts hX hk'
  have h' : q * (r * k) = q' * (r' * k') := by rw [← mul_assoc, ← mul_assoc]; exact h
  have hdvd : q ∣ q' * (r' * k') := ⟨r * k, h'.symm⟩
  rcases (Nat.Prime.dvd_mul hqp).1 hdvd with h1 | h1
  · have hqq : q = q' := (Nat.prime_dvd_prime_iff_eq hqp hq'p).1 h1
    subst hqq
    have h2 : r * k = r' * k' := Nat.eq_of_mul_eq_mul_left hqp.pos h'
    obtain ⟨h3, h4⟩ := rk_inj hX hr hk' hr' h2
    exact ⟨rfl, h3, h4⟩
  · exfalso
    have hr'0 : 0 < r' := (r_facts hX hr').1.pos
    have h2 : q ≤ r' * k' := Nat.le_of_dvd (Nat.mul_pos hr'0 hk'1) h1
    have h3 : (q : ℝ) ≤ (r' : ℝ) * k' := by exact_mod_cast h2
    have h4 := rk_le hX hr'2 hk'2
    have h5 : X ^ ((1 : ℝ) / 10) ≤ X ^ ((7 : ℝ) / 20) :=
      Real.rpow_le_rpow_of_exponent_le hX (by norm_num)
    linarith

/-- Chebyshev for the prime `p` of a tuple: `π(X/(qrk)) ≤ 15 (X/log X) · 1/(qrk)`. -/
theorem card_p_le {X : ℝ} (hX : 1 < X) {q r k : ℕ} (hq : q ∈ Qset X) (hr : r ∈ Rset X)
    (hk : k ∈ Kset X) :
    ((Nat.primesLE ⌊X / ((q : ℝ) * r * k)⌋₊).card : ℝ) ≤
      15 * X / Real.log X * (1 / (q : ℝ) * (1 / (r : ℝ) * (1 / (k : ℝ)))) := by
  have hX1 : 1 ≤ X := hX.le
  have hX0 : 0 < X := by linarith
  obtain ⟨hqp, _, hq2⟩ := q_facts hX1 hq
  obtain ⟨hrp, _, hr2⟩ := r_facts hX1 hr
  obtain ⟨hk1, _, hk2⟩ := k_facts hX1 hk
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hqp.pos
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hrp.pos
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
  have hqrk0 : (0 : ℝ) < (q : ℝ) * r * k := by positivity
  have hqrk := qrk_le hX1 hq2 hr2 hk2
  set x := X / ((q : ℝ) * r * k) with hxdef
  have hx8 : X ^ ((8 : ℝ) / 15) ≤ x := by
    have e : X ^ ((8 : ℝ) / 15) = X / X ^ ((7 : ℝ) / 15) := by
      rw [show (8 : ℝ) / 15 = 1 - 7 / 15 by norm_num, Real.rpow_sub hX0, Real.rpow_one]
    rw [e, hxdef]
    exact div_le_div_of_nonneg_left hX0.le hqrk0 hqrk
  have hx1 : 1 < x := lt_of_lt_of_le (Real.one_lt_rpow hX (by norm_num)) hx8
  have hlX : 0 < Real.log X := Real.log_pos hX
  have hlx : (8 / 15) * Real.log X ≤ Real.log x := by
    have := Real.log_le_log (Real.rpow_pos_of_pos hX0 _) hx8
    rwa [Real.log_rpow hX0] at this
  have h1 := card_primesLE_le hx1
  have h2 : 8 * x / Real.log x ≤ 8 * x / ((8 / 15) * Real.log X) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) hlx
  have e : 8 * x / ((8 / 15) * Real.log X) =
      15 * X / Real.log X * (1 / (q : ℝ) * (1 / (r : ℝ) * (1 / (k : ℝ)))) := by
    rw [hxdef]
    field_simp
  linarith

/-! ## The reciprocal sums over the four exceptional kinds of triples -/

theorem inv_triple_nonneg (τ : ℕ × ℕ × ℕ) :
    0 ≤ 1 / (τ.1 : ℝ) * (1 / (τ.2.1 : ℝ) * (1 / (τ.2.2 : ℝ))) := by positivity

open Classical in
/-- Triples with `k ∈ E`. -/
theorem sum_k_bad (X : ℝ) (E : Set ℕ) :
    ∑ τ ∈ (Qset X ×ˢ (Rset X ×ˢ Kset X)).filter (fun τ => τ.2.2 ∈ E),
      1 / (τ.1 : ℝ) * (1 / (τ.2.1 : ℝ) * (1 / (τ.2.2 : ℝ))) ≤
    (∑ q ∈ Qset X, (1 : ℝ) / q) * ((∑ r ∈ Rset X, (1 : ℝ) / r) *
      (∑ k ∈ (Finset.Icc 1 ⌊X ^ ((1 : ℝ) / 60)⌋₊).filter (· ∈ E), (1 : ℝ) / k)) := by
  have hsub : (Qset X ×ˢ (Rset X ×ˢ Kset X)).filter (fun τ => τ.2.2 ∈ E) ⊆
      Qset X ×ˢ (Rset X ×ˢ (Finset.Icc 1 ⌊X ^ ((1 : ℝ) / 60)⌋₊).filter (· ∈ E)) := by
    intro τ hτ
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_product] at hτ
    rw [Finset.mem_product, Finset.mem_product, mem_cntFinset]
    refine ⟨hτ.1.1, hτ.1.2.1, ?_, hτ.2⟩
    have := hτ.1.2.2
    rw [Kset, Finset.mem_filter, Finset.mem_Icc] at this
    exact this.1
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun τ _ _ => inv_triple_nonneg τ)).trans ?_
  exact le_of_eq (sum_prod3 _ _ _ (fun q => 1 / (q : ℝ)) (fun r => 1 / (r : ℝ))
    (fun k => 1 / (k : ℝ)))

open Classical in
/-- Triples with `r k ∈ E`. -/
theorem sum_rk_bad {X : ℝ} (hX : 1 ≤ X) (E : Set ℕ) :
    ∑ τ ∈ (Qset X ×ˢ (Rset X ×ˢ Kset X)).filter (fun τ => τ.2.1 * τ.2.2 ∈ E),
      1 / (τ.1 : ℝ) * (1 / (τ.2.1 : ℝ) * (1 / (τ.2.2 : ℝ))) ≤
    (∑ q ∈ Qset X, (1 : ℝ) / q) *
      (∑ l ∈ (Finset.Icc 1 ⌊X ^ ((1 : ℝ) / 10)⌋₊).filter (· ∈ E), (1 : ℝ) / l) := by
  set S2 := (Rset X ×ˢ Kset X).filter (fun σ => σ.1 * σ.2 ∈ E) with hS2
  have hsub : (Qset X ×ˢ (Rset X ×ˢ Kset X)).filter (fun τ => τ.2.1 * τ.2.2 ∈ E) ⊆
      Qset X ×ˢ S2 := by
    intro τ hτ
    rw [Finset.mem_filter, Finset.mem_product] at hτ
    rw [Finset.mem_product, hS2, Finset.mem_filter]
    exact ⟨hτ.1.1, hτ.1.2, hτ.2⟩
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun τ _ _ => inv_triple_nonneg τ)).trans ?_
  rw [sum_prod2 (Qset X) S2 (fun q => (1 : ℝ) / q)
    (fun σ => 1 / (σ.1 : ℝ) * (1 / (σ.2 : ℝ)))]
  apply mul_le_mul_of_nonneg_left _ (Finset.sum_nonneg (fun _ _ => by positivity))
  have hinj : Set.InjOn (fun σ : ℕ × ℕ => σ.1 * σ.2) (S2 : Set (ℕ × ℕ)) := by
    rintro ⟨r, k⟩ hσ ⟨r', k'⟩ hσ' h
    simp only [Finset.mem_coe, hS2, Finset.mem_filter, Finset.mem_product] at hσ hσ'
    simp only at h
    obtain ⟨h1, h2⟩ := rk_inj hX hσ.1.1 hσ'.1.2 hσ'.1.1 h
    rw [h1, h2]
  have e : ∑ σ ∈ S2, 1 / (σ.1 : ℝ) * (1 / (σ.2 : ℝ)) =
      ∑ l ∈ S2.image (fun σ : ℕ × ℕ => σ.1 * σ.2), (1 : ℝ) / l := by
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    push_cast
    rw [one_div_mul_one_div]
  rw [e]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
  intro l hl
  obtain ⟨⟨r, k⟩, hσ, rfl⟩ := Finset.mem_image.1 hl
  rw [hS2, Finset.mem_filter, Finset.mem_product] at hσ
  obtain ⟨hrp, -, hr2⟩ := r_facts hX hσ.1.1
  obtain ⟨hk1, -, hk2⟩ := k_facts hX hσ.1.2
  rw [mem_cntFinset]
  refine ⟨⟨Nat.mul_pos hrp.pos hk1, Nat.le_floor ?_⟩, hσ.2⟩
  push_cast
  exact rk_le hX hr2 hk2

open Classical in
/-- Triples with `q r k ∈ E`. -/
theorem sum_qrk_bad {X : ℝ} (hX : 1 ≤ X) (E : Set ℕ) :
    ∑ τ ∈ (Qset X ×ˢ (Rset X ×ˢ Kset X)).filter (fun τ => τ.1 * τ.2.1 * τ.2.2 ∈ E),
      1 / (τ.1 : ℝ) * (1 / (τ.2.1 : ℝ) * (1 / (τ.2.2 : ℝ))) ≤
    ∑ n ∈ (Finset.Icc 1 ⌊X ^ ((7 : ℝ) / 15)⌋₊).filter (· ∈ E), (1 : ℝ) / n := by
  set S3 := (Qset X ×ˢ (Rset X ×ˢ Kset X)).filter (fun τ => τ.1 * τ.2.1 * τ.2.2 ∈ E) with hS3
  have hinj : Set.InjOn (fun τ : ℕ × ℕ × ℕ => τ.1 * τ.2.1 * τ.2.2) (S3 : Set (ℕ × ℕ × ℕ)) := by
    rintro ⟨q, r, k⟩ hτ ⟨q', r', k'⟩ hτ' h
    simp only [Finset.mem_coe, hS3, Finset.mem_filter, Finset.mem_product] at hτ hτ'
    simp only at h
    obtain ⟨h1, h2, h3⟩ := qrk_inj hX hτ.1.1 hτ.1.2.1 hτ'.1.1 hτ'.1.2.1 hτ'.1.2.2 h
    rw [h1, h2, h3]
  have e : ∑ τ ∈ S3, 1 / (τ.1 : ℝ) * (1 / (τ.2.1 : ℝ) * (1 / (τ.2.2 : ℝ))) =
      ∑ n ∈ S3.image (fun τ : ℕ × ℕ × ℕ => τ.1 * τ.2.1 * τ.2.2), (1 : ℝ) / n := by
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl (fun τ _ => ?_)
    push_cast
    rw [one_div_mul_one_div, one_div_mul_one_div, mul_assoc]
  rw [e]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
  intro n hn
  obtain ⟨⟨q, r, k⟩, hτ, rfl⟩ := Finset.mem_image.1 hn
  rw [hS3, Finset.mem_filter, Finset.mem_product, Finset.mem_product] at hτ
  obtain ⟨hqp, -, hq2⟩ := q_facts hX hτ.1.1
  obtain ⟨hrp, -, hr2⟩ := r_facts hX hτ.1.2.1
  obtain ⟨hk1, -, hk2⟩ := k_facts hX hτ.1.2.2
  rw [mem_cntFinset]
  refine ⟨⟨Nat.mul_pos (Nat.mul_pos hqp.pos hrp.pos) hk1, Nat.le_floor ?_⟩, hτ.2⟩
  push_cast
  exact qrk_le hX hq2 hr2 hk2

open Classical in
/-- Triples whose `k` has a prime factor in `(Y, y(X)]`. -/
theorem sum_mid_bad {X : ℝ} (hX : 1 ≤ X) :
    ∑ τ ∈ (Qset X ×ˢ (Rset X ×ˢ Kset X)).filter
        (fun τ => ∃ ℓ : ℕ, ℓ ∈ τ.2.2.primeFactors ∧ SV.Ycut X < ℓ ∧ (ℓ : ℝ) ≤ SV.yOf X),
      1 / (τ.1 : ℝ) * (1 / (τ.2.1 : ℝ) * (1 / (τ.2.2 : ℝ))) ≤
    (∑ q ∈ Qset X, (1 : ℝ) / q) * ((∑ r ∈ Rset X, (1 : ℝ) / r) *
      ((∑ ℓ ∈ SV.primesIoc (SV.Ycut X) (SV.yOf X), (1 : ℝ) / ℓ) *
        ∑ j ∈ Finset.Icc 1 ⌊X ^ ((1 : ℝ) / 60)⌋₊, (1 : ℝ) / j)) := by
  set K5 := (Kset X).filter (fun k => ∃ ℓ : ℕ, ℓ ∈ k.primeFactors ∧ SV.Ycut X < ℓ ∧ (ℓ : ℝ) ≤ SV.yOf X)
    with hK5
  have hsub : (Qset X ×ˢ (Rset X ×ˢ Kset X)).filter
      (fun τ => ∃ ℓ : ℕ, ℓ ∈ τ.2.2.primeFactors ∧ SV.Ycut X < ℓ ∧ (ℓ : ℝ) ≤ SV.yOf X) ⊆
      Qset X ×ˢ (Rset X ×ˢ K5) := by
    intro τ hτ
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_product] at hτ
    rw [Finset.mem_product, Finset.mem_product, hK5, Finset.mem_filter]
    exact ⟨hτ.1.1, hτ.1.2.1, hτ.1.2.2, hτ.2⟩
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun τ _ _ => inv_triple_nonneg τ)).trans ?_
  rw [sum_prod3 _ _ _ (fun q => 1 / (q : ℝ)) (fun r => 1 / (r : ℝ)) (fun k => 1 / (k : ℝ))]
  have hq0 : 0 ≤ ∑ q ∈ Qset X, (1 : ℝ) / q := Finset.sum_nonneg (fun _ _ => by positivity)
  have hr0 : 0 ≤ ∑ r ∈ Rset X, (1 : ℝ) / r := Finset.sum_nonneg (fun _ _ => by positivity)
  apply mul_le_mul_of_nonneg_left _ hq0
  apply mul_le_mul_of_nonneg_left _ hr0
  apply sum_inv_multiples_le
  · intro ℓ hℓ
    exact (mem_primesIoc.1 hℓ).2.1.one_lt.le
  · intro k hk
    rw [hK5, Finset.mem_filter] at hk
    obtain ⟨hk1, -, hk2⟩ := k_facts hX hk.1
    obtain ⟨ℓ, hℓ, h1, h2⟩ := hk.2
    have hℓ' := Nat.mem_primeFactors.1 hℓ
    refine ⟨hk1, Nat.le_floor hk2, ℓ, mem_primesIoc.2 ⟨Nat.le_floor h2, hℓ'.1, h1⟩, hℓ'.2.1⟩

/-! ## The regular subfamily -/

/-- A tuple `(p, q, r, k)` is *retained* if none of `k, ℓ = rk, n = qrk, M = pqrk` lies in the
exceptional set `E`, and `k` has no prime factor in `(Y, y(X)]` (EP1054.tex lines 1421–1441). -/
def GoodT (E : Set ℕ) (X : ℝ) (p q r k : ℕ) : Prop :=
  k ∉ E ∧ r * k ∉ E ∧ q * r * k ∉ E ∧ p * q * r * k ∉ E ∧
    ¬ ∃ ℓ : ℕ, ℓ ∈ k.primeFactors ∧ SV.Ycut X < ℓ ∧ (ℓ : ℝ) ≤ SV.yOf X

open Classical in
/-- The subfamily `𝒜(X) ⊆ 𝒜₀(X)` of `lem:sv-regular`: the members all of whose tuples are
retained. -/
noncomputable def famA (D : ℕ) (E : Set ℕ) (X : ℝ) : Finset ℕ :=
  (S4a.A0 D X).filter (fun M => ∀ p q r k : ℕ, S4a.A0Tuple D X p q r k → M = p * q * r * k →
    GoodT E X p q r k)

open Classical in
theorem mem_famA {D : ℕ} {E : Set ℕ} {X : ℝ} {M : ℕ} :
    M ∈ famA D E X ↔ M ∈ S4a.A0 D X ∧ ∀ p q r k : ℕ, S4a.A0Tuple D X p q r k →
      M = p * q * r * k → GoodT E X p q r k := by
  unfold famA
  rw [Finset.mem_filter]

open Classical in
/-- The members of `𝒜₀(X)` with a tuple having the property `Φ(q, r, k)`. -/
noncomputable def Sset (D : ℕ) (X : ℝ) (Φ : ℕ → ℕ → ℕ → Prop) : Finset ℕ :=
  (S4a.A0 D X).filter (fun M => ∃ p q r k : ℕ, S4a.A0Tuple D X p q r k ∧
    M = p * q * r * k ∧ Φ q r k)

open Classical in
theorem mem_Sset {D : ℕ} {X : ℝ} {Φ : ℕ → ℕ → ℕ → Prop} {M : ℕ} :
    M ∈ Sset D X Φ ↔ M ∈ S4a.A0 D X ∧ ∃ p q r k : ℕ, S4a.A0Tuple D X p q r k ∧
      M = p * q * r * k ∧ Φ q r k := by
  unfold Sset
  rw [Finset.mem_filter]

open Classical in
/-- An upper-bound estimate for the prime `p` (EP1054.tex lines 1450–1456). -/
theorem card_Sset_le (D : ℕ) {X : ℝ} (hX : 1 < X) (Φ : ℕ → ℕ → ℕ → Prop) :
    ((Sset D X Φ).card : ℝ) ≤ 15 * X / Real.log X *
      ∑ τ ∈ (Qset X ×ˢ (Rset X ×ˢ Kset X)).filter (fun τ => Φ τ.1 τ.2.1 τ.2.2),
        1 / (τ.1 : ℝ) * (1 / (τ.2.1 : ℝ) * (1 / (τ.2.2 : ℝ))) := by
  have h1 := card_tuples_le D (by linarith : (0 : ℝ) ≤ X) Φ
  have h1' : ((Sset D X Φ).card : ℝ) ≤
      ∑ τ ∈ (Qset X ×ˢ (Rset X ×ˢ Kset X)).filter (fun τ => Φ τ.1 τ.2.1 τ.2.2),
        ((Nat.primesLE ⌊X / ((τ.1 : ℝ) * τ.2.1 * τ.2.2)⌋₊).card : ℝ) := by
    unfold Sset
    exact_mod_cast h1
  rw [Finset.mul_sum]
  refine h1'.trans (Finset.sum_le_sum (fun τ hτ => ?_))
  rw [Finset.mem_filter, Finset.mem_product, Finset.mem_product] at hτ
  exact card_p_le hX hτ.1.1 hτ.1.2.1 hτ.1.2.2

open Classical in
/-- Monotonicity of the triple sums in the property. -/
theorem sum_R3_mono (X : ℝ) (Φ : ℕ → ℕ → ℕ → Prop) (P : ℕ × ℕ × ℕ → Prop) [DecidablePred P]
    (h : ∀ q r k, Φ q r k → P (q, r, k)) :
    ∑ τ ∈ (Qset X ×ˢ (Rset X ×ˢ Kset X)).filter (fun τ => Φ τ.1 τ.2.1 τ.2.2),
        1 / (τ.1 : ℝ) * (1 / (τ.2.1 : ℝ) * (1 / (τ.2.2 : ℝ))) ≤
      ∑ τ ∈ (Qset X ×ˢ (Rset X ×ˢ Kset X)).filter P,
        1 / (τ.1 : ℝ) * (1 / (τ.2.1 : ℝ) * (1 / (τ.2.2 : ℝ))) := by
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun τ hτ => ?_)
    (fun τ _ _ => inv_triple_nonneg τ)
  rw [Finset.mem_filter] at hτ ⊢
  exact ⟨hτ.1, h _ _ _ hτ.2⟩

/-- The four exceptional properties of a triple. -/
def Phi1 (E : Set ℕ) : ℕ → ℕ → ℕ → Prop := fun _ _ k => k ∈ E

/-- See `Phi1`. -/
def Phi2 (E : Set ℕ) : ℕ → ℕ → ℕ → Prop := fun _ r k => r * k ∈ E

/-- See `Phi1`. -/
def Phi3 (E : Set ℕ) : ℕ → ℕ → ℕ → Prop := fun q r k => q * r * k ∈ E

/-- See `Phi1`. -/
def Phi5 (X : ℝ) : ℕ → ℕ → ℕ → Prop := fun _ _ k =>
  ∃ ℓ : ℕ, ℓ ∈ k.primeFactors ∧ SV.Ycut X < ℓ ∧ (ℓ : ℝ) ≤ SV.yOf X

theorem isRough_mono {y z : ℝ} {n : ℕ} (h : y ≤ z) (hz : IsRough z n) : IsRough y n :=
  fun p hp => lt_of_le_of_lt h (hz p hp)

theorem isRough_one (y : ℝ) : IsRough y 1 := by
  intro p hp
  simp at hp

theorem one_lt_of_exp_two_le {X : ℝ} (hX : Real.exp 2 ≤ X) : 1 < X ∧ 2 ≤ Real.log X := by
  have h1 : (1 : ℝ) < Real.exp 2 := by
    have := Real.add_one_le_exp (2 : ℝ)
    linarith
  refine ⟨by linarith, ?_⟩
  have := Real.log_le_log (Real.exp_pos 2) hX
  rwa [Real.log_exp] at this

open Classical in
/-- The count of `lem:sv-regular`: `#𝒜(X) ≥ c₀ X / 2`, when the deletions are small
(EP1054.tex lines 1421–1458). -/
theorem famA_count {D : ℕ} {E : Set ℕ} {X c₀ : ℝ} (hc₀ : 0 < c₀) (hX : Real.exp 2 ≤ X)
    (hA0X : c₀ * X ≤ ((S4a.A0 D X).card : ℝ))
    (hEX : (cnt E X : ℝ) ≤ c₀ / 10 * X)
    (hSQ : ∑ q ∈ Qset X, (1 : ℝ) / q ≤ (11 / 30) / (7 / 20))
    (hSR : ∑ r ∈ Rset X, (1 : ℝ) / r ≤ (1 / 12) / (1 / 15))
    (hHK : ∑ n ∈ (Finset.Icc 1 ⌊X ^ ((1 : ℝ) / 60)⌋₊).filter (· ∈ E), (1 : ℝ) / n ≤
      c₀ / 55 * Real.log (X ^ ((1 : ℝ) / 60)))
    (hHL : ∑ n ∈ (Finset.Icc 1 ⌊X ^ ((1 : ℝ) / 10)⌋₊).filter (· ∈ E), (1 : ℝ) / n ≤
      c₀ / 55 * Real.log (X ^ ((1 : ℝ) / 10)))
    (hHN : ∑ n ∈ (Finset.Icc 1 ⌊X ^ ((7 : ℝ) / 15)⌋₊).filter (· ∈ E), (1 : ℝ) / n ≤
      c₀ / 55 * Real.log (X ^ ((7 : ℝ) / 15)))
    (hmid : ∑ ℓ ∈ SV.primesIoc (SV.Ycut X) (SV.yOf X), (1 : ℝ) / ℓ ≤ c₀ / 300) :
    c₀ / 2 * X ≤ ((famA D E X).card : ℝ) := by
  obtain ⟨hX1, hlX⟩ := one_lt_of_exp_two_le hX
  have hX1' : 1 ≤ X := hX1.le
  have hX0 : 0 < X := by linarith
  have hlX0 : 0 < Real.log X := by linarith
  rw [Real.log_rpow hX0] at hHK hHL hHN
  have hsub : S4a.A0 D X \ famA D E X ⊆ (S4a.A0 D X).filter (· ∈ E) ∪
      (Sset D X (Phi1 E) ∪ (Sset D X (Phi2 E) ∪ (Sset D X (Phi3 E) ∪ Sset D X (Phi5 X)))) := by
    intro M hM
    rw [Finset.mem_sdiff] at hM
    obtain ⟨hMA, hMf⟩ := hM
    rw [mem_famA] at hMf
    push Not at hMf
    obtain ⟨p, q, r, k, ht, hMe, hbad⟩ := hMf hMA
    rw [Finset.mem_union, Finset.mem_union, Finset.mem_union, Finset.mem_union, Finset.mem_filter,
      mem_Sset, mem_Sset, mem_Sset, mem_Sset]
    by_cases h1 : k ∈ E
    · exact Or.inr (Or.inl ⟨hMA, p, q, r, k, ht, hMe, h1⟩)
    by_cases h2 : r * k ∈ E
    · exact Or.inr (Or.inr (Or.inl ⟨hMA, p, q, r, k, ht, hMe, h2⟩))
    by_cases h3 : q * r * k ∈ E
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hMA, p, q, r, k, ht, hMe, h3⟩)))
    by_cases h4 : p * q * r * k ∈ E
    · exact Or.inl ⟨hMA, hMe ▸ h4⟩
    by_cases h5 : ∃ ℓ : ℕ, ℓ ∈ k.primeFactors ∧ SV.Ycut X < ℓ ∧ (ℓ : ℝ) ≤ SV.yOf X
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hMA, p, q, r, k, ht, hMe, h5⟩)))
    · exact absurd ⟨h1, h2, h3, h4, h5⟩ hbad
  have hcard_sd : ((S4a.A0 D X \ famA D E X).card : ℝ) ≤
      ((S4a.A0 D X).filter (· ∈ E)).card + ((Sset D X (Phi1 E)).card +
        ((Sset D X (Phi2 E)).card + ((Sset D X (Phi3 E)).card + (Sset D X (Phi5 X)).card))) := by
    have := (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_left ((Finset.card_union_le _ _).trans (Nat.add_le_add_left
        ((Finset.card_union_le _ _).trans (Nat.add_le_add_left
          (Finset.card_union_le _ _) _)) _)) _))
    exact_mod_cast this
  have hsplit : ((S4a.A0 D X).card : ℝ) =
      ((S4a.A0 D X \ famA D E X).card : ℝ) + ((famA D E X).card : ℝ) := by
    exact_mod_cast (Finset.card_sdiff_add_card_eq_card
      (fun M hM => (mem_famA.1 hM).1)).symm
  have hEX' : (((S4a.A0 D X).filter (· ∈ E)).card : ℝ) ≤ c₀ / 10 * X := by
    have h1 : ((S4a.A0 D X).filter (· ∈ E)).card ≤ cnt {n : ℕ | n ∈ E} X :=
      card_filter_le_cnt (fun M hM => (mem_A0 hM).1) (· ∈ E)
    exact (Nat.cast_le.2 h1).trans hEX
  -- the reciprocal sums
  have hSQ2 : ∑ q ∈ Qset X, (1 : ℝ) / q ≤ 2 := hSQ.trans (by norm_num)
  have hSR2 : ∑ r ∈ Rset X, (1 : ℝ) / r ≤ 2 := hSR.trans (by norm_num)
  have hHK0 : 0 ≤ ∑ k ∈ (Finset.Icc 1 ⌊X ^ ((1 : ℝ) / 60)⌋₊).filter (· ∈ E), (1 : ℝ) / k :=
    Finset.sum_nonneg (fun _ _ => by positivity)
  have hS₁ : ∑ τ ∈ (Qset X ×ˢ (Rset X ×ˢ Kset X)).filter (fun τ => Phi1 E τ.1 τ.2.1 τ.2.2),
      1 / (τ.1 : ℝ) * (1 / (τ.2.1 : ℝ) * (1 / (τ.2.2 : ℝ))) ≤
      4 * (c₀ / 55 * (1 / 60)) * Real.log X := by
    refine (sum_R3_mono X (Phi1 E) (fun τ => τ.2.2 ∈ E) (fun _ _ _ h => h)).trans
      ((sum_k_bad X E).trans ?_)
    calc (∑ q ∈ Qset X, (1 : ℝ) / q) * ((∑ r ∈ Rset X, (1 : ℝ) / r) *
          (∑ k ∈ (Finset.Icc 1 ⌊X ^ ((1 : ℝ) / 60)⌋₊).filter (· ∈ E), (1 : ℝ) / k))
        ≤ 2 * (2 * (c₀ / 55 * (1 / 60 * Real.log X))) := by
          apply mul_le_mul hSQ2 _ (by positivity) (by norm_num)
          exact mul_le_mul hSR2 hHK hHK0 (by norm_num)
      _ = 4 * (c₀ / 55 * (1 / 60)) * Real.log X := by ring
  have hS₂ : ∑ τ ∈ (Qset X ×ˢ (Rset X ×ˢ Kset X)).filter (fun τ => Phi2 E τ.1 τ.2.1 τ.2.2),
      1 / (τ.1 : ℝ) * (1 / (τ.2.1 : ℝ) * (1 / (τ.2.2 : ℝ))) ≤
      2 * (c₀ / 55 * (1 / 10)) * Real.log X := by
    refine (sum_R3_mono X (Phi2 E) (fun τ => τ.2.1 * τ.2.2 ∈ E) (fun _ _ _ h => h)).trans
      ((sum_rk_bad hX1' E).trans ?_)
    calc _ ≤ 2 * (c₀ / 55 * (1 / 10 * Real.log X)) :=
          mul_le_mul hSQ2 hHL (Finset.sum_nonneg (fun _ _ => by positivity)) (by norm_num)
      _ = 2 * (c₀ / 55 * (1 / 10)) * Real.log X := by ring
  have hS₃ : ∑ τ ∈ (Qset X ×ˢ (Rset X ×ˢ Kset X)).filter (fun τ => Phi3 E τ.1 τ.2.1 τ.2.2),
      1 / (τ.1 : ℝ) * (1 / (τ.2.1 : ℝ) * (1 / (τ.2.2 : ℝ))) ≤
      c₀ / 55 * (7 / 15) * Real.log X := by
    refine (sum_R3_mono X (Phi3 E) (fun τ => τ.1 * τ.2.1 * τ.2.2 ∈ E) (fun _ _ _ h => h)).trans
      ((sum_qrk_bad hX1' E).trans ?_)
    calc _ ≤ c₀ / 55 * (7 / 15 * Real.log X) := hHN
      _ = c₀ / 55 * (7 / 15) * Real.log X := by ring
  have hharm : ∑ j ∈ Finset.Icc 1 ⌊X ^ ((1 : ℝ) / 60)⌋₊, (1 : ℝ) / j ≤ Real.log X := by
    have h1 := sum_Icc_inv_le_one_add_log ⌊X ^ ((1 : ℝ) / 60)⌋₊
    have h2 : Real.log ⌊X ^ ((1 : ℝ) / 60)⌋₊ ≤ Real.log X / 60 := by
      rcases Nat.eq_zero_or_pos ⌊X ^ ((1 : ℝ) / 60)⌋₊ with h0 | hpos
      · rw [h0, Nat.cast_zero, Real.log_zero]
        positivity
      · have := Real.log_le_log (by exact_mod_cast hpos)
          (Nat.floor_le (Real.rpow_nonneg hX0.le ((1 : ℝ) / 60)))
        rw [Real.log_rpow hX0] at this
        linarith
    linarith
  have hS₅ : ∑ τ ∈ (Qset X ×ˢ (Rset X ×ˢ Kset X)).filter (fun τ => Phi5 X τ.1 τ.2.1 τ.2.2),
      1 / (τ.1 : ℝ) * (1 / (τ.2.1 : ℝ) * (1 / (τ.2.2 : ℝ))) ≤
      4 * (c₀ / 300) * Real.log X := by
    refine (sum_R3_mono X (Phi5 X)
      (fun τ => ∃ ℓ : ℕ, ℓ ∈ τ.2.2.primeFactors ∧ SV.Ycut X < ℓ ∧ (ℓ : ℝ) ≤ SV.yOf X)
      (fun _ _ _ h => h)).trans ((sum_mid_bad hX1').trans ?_)
    have hj0 : 0 ≤ ∑ j ∈ Finset.Icc 1 ⌊X ^ ((1 : ℝ) / 60)⌋₊, (1 : ℝ) / j :=
      Finset.sum_nonneg (fun _ _ => by positivity)
    calc _ ≤ 2 * (2 * (c₀ / 300 * Real.log X)) := by
          apply mul_le_mul hSQ2 _ (by positivity) (by norm_num)
          apply mul_le_mul hSR2 _ (by positivity) (by norm_num)
          exact mul_le_mul hmid hharm hj0 (by positivity)
      _ = 4 * (c₀ / 300) * Real.log X := by ring
  have hW : 0 ≤ 15 * X / Real.log X := by positivity
  have key : ∀ c : ℝ, 15 * X / Real.log X * (c * Real.log X) = 15 * X * c := fun c => by
    field_simp
  have b1 := (card_Sset_le D hX1 (Phi1 E)).trans
    ((mul_le_mul_of_nonneg_left hS₁ hW).trans (le_of_eq (key _)))
  have b2 := (card_Sset_le D hX1 (Phi2 E)).trans
    ((mul_le_mul_of_nonneg_left hS₂ hW).trans (le_of_eq (key _)))
  have b3 := (card_Sset_le D hX1 (Phi3 E)).trans
    ((mul_le_mul_of_nonneg_left hS₃ hW).trans (le_of_eq (key _)))
  have b5 := (card_Sset_le D hX1 (Phi5 X)).trans
    ((mul_le_mul_of_nonneg_left hS₅ hW).trans (le_of_eq (key _)))
  have e1 : 15 * X * (4 * (c₀ / 55 * (1 / 60))) + 15 * X * (2 * (c₀ / 55 * (1 / 10))) +
      15 * X * (c₀ / 55 * (7 / 15)) + 15 * X * (4 * (c₀ / 300)) = c₀ / 5 * X + c₀ / 5 * X := by
    ring
  linarith

theorem aliquot_ne_zero_of {δ : ℝ} (hδ : 0 < δ) {t : ℕ} (h : 1 / δ < (aliquot t : ℝ) / t) :
    aliquot t ≠ 0 := by
  intro h0
  rw [h0, Nat.cast_zero, zero_div] at h
  have : 0 < 1 / δ := by positivity
  linarith

/-- The Luca–Pomerance conclusions at a level `t = a k` of `M = t b` give (i)–(ii) there. -/
theorem level_regular {Y yX Z : ℝ} {t a b k M : ℕ}
    (ht : t = a * k) (hM : M = t * b) (hk0 : k ≠ 0) (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (hs0 : aliquot t ≠ 0)
    (hLP : (∀ p : ℕ, p.Prime → (p : ℝ) ≤ yLP t → t.factorization p < (sig t).factorization p) ∧
      IsSmooth (yLP t) (Nat.gcd t (sig t)) ∧
      (∀ p : ℕ, p.Prime → (p : ℝ) ≤ yLP t → p ∣ sig t / Nat.gcd t (sig t)) ∧
      IsRough (yLP t) (aliquot t / Nat.gcd t (sig t)))
    (hY : Y ≤ yLP t) (hyt : yLP t ≤ yX) (hyZ : yX < Z) (hYZ : Y ≤ Z)
    (ha : IsRough Z a) (hb : IsRough Z b)
    (hmidk : ¬ ∃ ℓ : ℕ, ℓ ∈ k.primeFactors ∧ Y < ℓ ∧ (ℓ : ℝ) ≤ yX) :
    SV.RegularAt Y (SV.smoothPart Y M) t := by
  obtain ⟨h1, h2, h3, h4⟩ := hLP
  have ht0 : t ≠ 0 := by rw [ht]; exact mul_ne_zero ha0 hk0
  refine regularAt_of ht0 hs0 h1 h2 h3 h4 hY ?_ ?_
  · intro ℓ hℓ hℓ'
    have hℓp := Nat.mem_primeFactors.1 hℓ
    rw [ht] at hℓp
    rcases (Nat.Prime.dvd_mul hℓp.1).1 hℓp.2.1 with h | h
    · have := ha ℓ (Nat.mem_primeFactors.2 ⟨hℓp.1, h, ha0⟩)
      linarith [hℓ'.2]
    · exact hmidk ⟨ℓ, Nat.mem_primeFactors.2 ⟨hℓp.1, h, hk0⟩, hℓ'.1, hℓ'.2.trans hyt⟩
  · rw [hM]
    exact smoothPart_mul_rough_right ht0 hb0 (isRough_mono hYZ hb)

/-- The properties of `lem:sv-regular` for every member of `𝒜(X)` (EP1054.tex lines
1460–1479). -/
theorem famA_regular {D : ℕ} {E E₁ E₂ E₃ : Set ℕ} {X δ Cδ : ℝ} (hδ : 0 < δ)
    (hX : Real.exp 2 ≤ X)
    (hTwo : ∀ p q r k : ℕ, S4a.A0Tuple D X p q r k →
      ∀ t : ℕ, (t = k ∨ t = r * k ∨ t = q * r * k ∨ t = p * q * r * k) →
        1 / δ < (aliquot t : ℝ) / t ∧ (aliquot t : ℝ) / t < Cδ)
    (hQL : ∀ p q r k : ℕ, S4a.A0Tuple D X p q r k →
      ((q * r * k : ℕ) : ℝ) ^ ((7 : ℝ) / 9) < (q : ℝ))
    (hLP1 : ∀ n : ℕ, n ∉ E₁ →
      (∀ p : ℕ, p.Prime → (p : ℝ) ≤ yLP n → n.factorization p < (sig n).factorization p) ∧
      IsSmooth (yLP n) (Nat.gcd n (sig n)) ∧
      (∀ p : ℕ, p.Prime → (p : ℝ) ≤ yLP n → p ∣ sig n / Nat.gcd n (sig n)) ∧
      IsRough (yLP n) (aliquot n / Nat.gcd n (sig n)))
    (hLP2 : ∀ n : ℕ, n ∉ E₂ →
      (∃ p ∈ n.primeFactors, (n : ℝ) ^ ((7 : ℝ) / 9) < (p : ℝ)) →
      ∀ q₀ : ℕ, q₀.Prime → yLP n < (q₀ : ℝ) → (q₀ : ℝ) ≤ (n : ℝ) ^ ((10 : ℝ) / 27) →
        ¬ q₀ ^ 2 ∣ aliquot n)
    (hLP3 : ∀ n : ℕ, n ∉ E₃ →
      ∑ r ∈ (sig n).primeFactors.filter (fun r : ℕ => (logIt 2 (n : ℝ)) ^ 2 < (r : ℝ)),
        (1 : ℝ) / r ≤ 1)
    (hE1 : ∀ n, n ∉ E → n ∉ E₁) (hE2 : ∀ n, n ∉ E → n ∉ E₂) (hE3 : ∀ n, n ∉ E → n ∉ E₃)
    (hE4 : ∀ n, n ∉ E →
      ¬ ((aliquot n : ℝ) / n + 1 < (aliquot (aliquot n) : ℝ) / (aliquot n : ℝ)))
    (hXu : uThr ≤ X ^ ((1 : ℝ) / 120)) (hyZ : SV.yOf X < X ^ ((1 : ℝ) / 15))
    (hX72 : 2 ≤ X ^ ((7 : ℝ) / 15)) (hX73 : 3 ≤ X ^ ((7 : ℝ) / 20)) :
    ∀ M ∈ famA D E X, SV.RegularMember D (Cδ + 2) X M := by
  obtain ⟨hX1, _⟩ := one_lt_of_exp_two_le hX
  have hX1' : 1 ≤ X := hX1.le
  have hX0 : 0 < X := by linarith
  intro M hM p q r k ht hMe
  obtain ⟨hMA, hMgood⟩ := mem_famA.1 hM
  obtain ⟨hkE, hrkE, hqrkE, hME, hmid⟩ := hMgood p q r k ht hMe
  have hMX : M ≤ ⌊X⌋₊ := (mem_A0 hMA).1.2
  have hMX' : (M : ℝ) ≤ X := (Nat.cast_le.2 hMX).trans (Nat.floor_le hX0.le)
  have hts := hTwo p q r k ht
  have hQ := hQL p q r k ht
  obtain ⟨hpp, hqp, hrp, -, hk1, hk2, hr1, hr2, hq1, hq2, hp1, -⟩ := ht
  -- sizes
  have hU0 : 0 ≤ X ^ ((1 : ℝ) / 120) := Real.rpow_nonneg hX0.le _
  have hk0R : (0 : ℝ) < k := lt_of_le_of_lt hU0 hk1
  have hk0 : k ≠ 0 := by
    intro h
    rw [h, Nat.cast_zero] at hk0R
    exact lt_irrefl _ hk0R
  have hqrk := qrk_le hX1' hq2 hr2 hk2
  have hr0R : (0 : ℝ) < r := by exact_mod_cast hrp.pos
  have hq0R : (0 : ℝ) < q := by exact_mod_cast hqp.pos
  have hrZ : X ^ ((1 : ℝ) / 15) < r := hr1
  have hqZ : X ^ ((1 : ℝ) / 15) < q :=
    lt_of_le_of_lt (Real.rpow_le_rpow_of_exponent_le hX1' (by norm_num)) hq1
  have hpZ : X ^ ((1 : ℝ) / 15) < p := by
    have hqrk0 : (0 : ℝ) < (q : ℝ) * r * k := by positivity
    have h1 : X ^ ((8 : ℝ) / 15) / 2 ≤ X / (2 * (q : ℝ) * r * k) := by
      have e : X ^ ((8 : ℝ) / 15) = X / X ^ ((7 : ℝ) / 15) := by
        rw [show (8 : ℝ) / 15 = 1 - 7 / 15 by norm_num, Real.rpow_sub hX0, Real.rpow_one]
      rw [e, div_div, show 2 * (q : ℝ) * r * k = 2 * ((q : ℝ) * r * k) by ring,
        div_le_div_iff₀ (by positivity) (by positivity)]
      have := mul_le_mul_of_nonneg_left hqrk (by positivity : (0 : ℝ) ≤ X * 2)
      linarith
    have h2 : X ^ ((1 : ℝ) / 15) ≤ X ^ ((8 : ℝ) / 15) / 2 := by
      have e : X ^ ((8 : ℝ) / 15) = X ^ ((1 : ℝ) / 15) * X ^ ((7 : ℝ) / 15) := by
        rw [← Real.rpow_add hX0]
        norm_num
      rw [e]
      have := Real.rpow_nonneg hX0.le ((1 : ℝ) / 15)
      nlinarith
    linarith
  -- the levels
  have hlev : ∀ t : ℕ, k ≤ t → t ≤ M → SV.Ycut X ≤ yLP t ∧ yLP t ≤ SV.yOf X := by
    intro t hkt htM
    have hkt' : (k : ℝ) ≤ t := by exact_mod_cast hkt
    have htu : uThr ≤ (t : ℝ) := hXu.trans (hk1.le.trans hkt')
    have htX : (t : ℝ) ≤ X := (Nat.cast_le.2 htM).trans hMX'
    refine ⟨?_, yOf_mono htu htX⟩
    rw [yLP_eq_yOf]
    exact yOf_mono hXu (hk1.le.trans hkt')
  have hpqr0 : p * q * r ≠ 0 :=
    Nat.mul_ne_zero (Nat.mul_ne_zero hpp.ne_zero hqp.ne_zero) hrp.ne_zero
  have hkM : k ≤ M := by
    rw [hMe]
    exact Nat.le_mul_of_pos_left k (Nat.pos_of_ne_zero hpqr0)
  have hrkM : r * k ≤ M := by
    rw [hMe, show p * q * r * k = p * q * (r * k) by ring]
    exact Nat.le_mul_of_pos_left _ (Nat.mul_pos hpp.pos hqp.pos)
  have hqrkM : q * r * k ≤ M := by
    rw [hMe, show p * q * r * k = p * (q * r * k) by ring]
    exact Nat.le_mul_of_pos_left _ hpp.pos
  have hkrk : k ≤ r * k := Nat.le_mul_of_pos_left k hrp.pos
  have hkqrk : k ≤ q * r * k := Nat.le_mul_of_pos_left k (Nat.mul_pos hqp.pos hrp.pos)
  have hYZ : SV.Ycut X ≤ X ^ ((1 : ℝ) / 15) := by
    have h := hlev k le_rfl hkM
    linarith [h.1, h.2]
  have hRp := isRough_prime hpp hpZ
  have hRq := isRough_prime hqp hqZ
  have hRr := isRough_prime hrp hrZ
  have hts_k := hts k (Or.inl rfl)
  have hts_rk := hts (r * k) (Or.inr (Or.inl rfl))
  have hts_qrk := hts (q * r * k) (Or.inr (Or.inr (Or.inl rfl)))
  have hts_M := hts (p * q * r * k) (Or.inr (Or.inr (Or.inr rfl)))
  rw [← hMe] at hts_M
  have hME' : M ∉ E := by rw [hMe]; exact hME
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact level_regular (a := 1) (b := p * q * r) (by ring) (by rw [hMe]; ring) hk0 one_ne_zero
      hpqr0 (aliquot_ne_zero_of hδ hts_k.1) (hLP1 k (hE1 k hkE))
      (hlev k le_rfl hkM).1 (hlev k le_rfl hkM).2 hyZ hYZ (isRough_one _)
      (isRough_mul (isRough_mul hRp hRq) hRr) hmid
  · exact level_regular (a := r) (b := p * q) rfl (by rw [hMe]; ring) hk0 hrp.ne_zero
      (Nat.mul_ne_zero hpp.ne_zero hqp.ne_zero) (aliquot_ne_zero_of hδ hts_rk.1)
      (hLP1 (r * k) (hE1 _ hrkE)) (hlev _ hkrk hrkM).1 (hlev _ hkrk hrkM).2 hyZ hYZ hRr
      (isRough_mul hRp hRq) hmid
  · exact level_regular (a := q * r) (b := p) rfl (by rw [hMe]; ring) hk0
      (Nat.mul_ne_zero hqp.ne_zero hrp.ne_zero) hpp.ne_zero (aliquot_ne_zero_of hδ hts_qrk.1)
      (hLP1 (q * r * k) (hE1 _ hqrkE)) (hlev _ hkqrk hqrkM).1 (hlev _ hkqrk hqrkM).2 hyZ hYZ
      (isRough_mul hRq hRr) hRp hmid
  · exact level_regular (a := p * q * r) (b := 1) (by rw [hMe]) (by ring) hk0 hpqr0
      one_ne_zero (aliquot_ne_zero_of hδ hts_M.1) (hLP1 M (hE1 _ hME'))
      (hlev M hkM le_rfl).1 (hlev M hkM le_rfl).2 hyZ hYZ
      (isRough_mul (isRough_mul hRp hRq) hRr) (isRough_one _) hmid
  · -- the square-divisibility exclusion at `n = qrk`
    have hq_mem : q ∈ (q * r * k).primeFactors :=
      Nat.mem_primeFactors.2 ⟨hqp, ⟨r * k, by ring⟩,
        Nat.mul_ne_zero (Nat.mul_ne_zero hqp.ne_zero hrp.ne_zero) hk0⟩
    exact hLP2 (q * r * k) (hE2 _ hqrkE) ⟨q, hq_mem, hQ⟩
  · -- `eq:sv-LP25` at `n = qrk`
    have hq3 : (3 : ℝ) ≤ q := hX73.trans hq1.le
    have h3 : 3 ≤ q := by exact_mod_cast hq3
    have hn3 : 3 ≤ q * r * k := by
      calc 3 ≤ q := h3
        _ ≤ q * r * k := by
          rw [show q * r * k = q * (r * k) by ring]
          exact Nat.le_mul_of_pos_right q (Nat.mul_pos hrp.pos (Nat.pos_of_ne_zero hk0))
    have hnX : ((q * r * k : ℕ) : ℝ) ≤ X := (Nat.cast_le.2 hqrkM).trans hMX'
    exact lp25_transfer hn3 hnX (hLP3 (q * r * k) (hE3 _ hqrkE))
  · -- `eq:sv-image-abundancy` at `n = qrk`
    exact imageAbundancy_of (aliquot_ne_zero_of hδ hts_qrk.1) hts_qrk.2 (hE4 _ hqrkE)

end Principia.Erdos1054.Proofs.SvRegular

namespace Principia.Erdos1054.Proofs

open Finset Filter Principia.Erdos1054 Principia.Erdos1054.Proofs.SvRegular

/-- **`lem:sv-regular`** (EP1054.tex lines 1394–1480). -/
theorem link_Lem_SvRegular : Principia.Erdos1054.Spine.Link_Lem_SvRegular := by
  intro hA0 hLP hHD hPol h2 δ hδ hδ1 D hD
  obtain ⟨hCount, _, hTwo, hQL⟩ := hA0
  obtain ⟨h21, h22, h25⟩ := hLP
  obtain ⟨c₀, hc₀, Xc, hXc⟩ := hCount δ hδ hδ1 D hD
  obtain ⟨Cδ, hCδ, Xt, hXt⟩ := hTwo δ hδ hδ1 D hD
  obtain ⟨Xq, hXq⟩ := hQL δ hδ hδ1 D hD
  obtain ⟨E₁, hE₁, hLP1⟩ := h21
  obtain ⟨E₂, hE₂, hLP2⟩ := h22
  obtain ⟨E₃, hE₃, hLP3⟩ := h25
  obtain ⟨E, hE, hEsub⟩ : ∃ E : Set ℕ, DensZero E ∧ E₁ ∪ E₂ ∪ E₃ ∪
      {n : ℕ | (aliquot n : ℝ) / n + 1 < (aliquot (aliquot n) : ℝ) / (aliquot n : ℝ)} ⊆ E :=
    ⟨_, densZero_union (densZero_union (densZero_union hE₁ hE₂) hE₃) hPol, subset_rfl⟩
  have hE1 : ∀ n, n ∉ E → n ∉ E₁ := fun n hn h => hn (hEsub (Or.inl (Or.inl (Or.inl h))))
  have hE2 : ∀ n, n ∉ E → n ∉ E₂ := fun n hn h => hn (hEsub (Or.inl (Or.inl (Or.inr h))))
  have hE3 : ∀ n, n ∉ E → n ∉ E₃ := fun n hn h => hn (hEsub (Or.inl (Or.inr h)))
  have hE4 : ∀ n, n ∉ E →
      ¬ ((aliquot n : ℝ) / n + 1 < (aliquot (aliquot n) : ℝ) / (aliquot n : ℝ)) :=
    fun n hn h => hn (hEsub (Or.inr h))
  obtain ⟨T₀, hT₀⟩ := hHD E hE (c₀ / 55) (by positivity)
  obtain ⟨XE, hXE⟩ := hE.exists_le_mul (by positivity : (0 : ℝ) < c₀ / 10)
  obtain ⟨XQ, hXQ⟩ := primesIoc_recip_le h2 (7 / 20) (11 / 30) (by norm_num) (by norm_num)
  obtain ⟨XR, hXR⟩ := primesIoc_recip_le h2 (1 / 15) (1 / 12) (by norm_num) (by norm_num)
  obtain ⟨Xm, hXm⟩ := mid_small h2 (c₀ / 300) (by positivity)
  obtain ⟨Xy, hXy⟩ := eventually_yOf_lt
  have hev : ∀ᶠ X : ℝ in atTop, famA D E X ⊆ S4a.A0 D X ∧
      c₀ / 2 * X ≤ ((famA D E X).card : ℝ) ∧
      ∀ M ∈ famA D E X, SV.RegularMember D (Cδ + 2) X M := by
    filter_upwards [eventually_ge_atTop Xc, eventually_ge_atTop Xt, eventually_ge_atTop Xq,
      eventually_ge_atTop XE, eventually_ge_atTop XQ, eventually_ge_atTop XR,
      eventually_ge_atTop Xm, eventually_ge_atTop Xy,
      eventually_ge_atTop (Real.exp 2),
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 120)).eventually_ge_atTop uThr,
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 7 / 15)).eventually_ge_atTop 2,
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 7 / 20)).eventually_ge_atTop 3,
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 60)).eventually_ge_atTop T₀]
      with X hXc' hXt' hXq' hXE' hXQ' hXR' hXm' hXy' hXe2 hXu hX72 hX73 hXT
    have hX1' : 1 ≤ X := (one_lt_of_exp_two_le hXe2).1.le
    have hθ : ∀ θ : ℝ, 1 / 60 ≤ θ → T₀ ≤ X ^ θ := fun θ hθ =>
      hXT.trans (Real.rpow_le_rpow_of_exponent_le hX1' hθ)
    refine ⟨fun M hM => (mem_famA.1 hM).1, ?_, ?_⟩
    · exact famA_count hc₀ hXe2 (hXc X hXc') (hXE X hXE') (hXQ X hXQ') (hXR X hXR')
        (hT₀ _ (hθ _ le_rfl)) (hT₀ _ (hθ _ (by norm_num))) (hT₀ _ (hθ _ (by norm_num)))
        (hXm X hXm')
    · exact famA_regular hδ hXe2 (hXt X hXt') (hXq X hXq') hLP1 hLP2 hLP3 hE1 hE2 hE3 hE4
        hXu (hXy X hXy') hX72 hX73
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.1 hev
  exact ⟨famA D E, c₀ / 2, by positivity, Cδ + 2, by positivity, X₀, fun X hX => hX₀ X hX⟩

end Principia.Erdos1054.Proofs
