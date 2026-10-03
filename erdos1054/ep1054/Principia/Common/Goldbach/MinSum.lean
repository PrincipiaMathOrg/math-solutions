/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Almost-all binary Goldbach, `MinSum`: the shared circle-method definitions, the min-sum workhorse, exponential sums, Type I/II

Ported **verbatim** from the circle-method half of the comparator-certified master
`GoldbachChainMaster.lean` (PNT+ workspace, lines 15807–17486; there
`#print axioms GoldbachChain.GoldbachReduction.almost_all_binary_goldbach_proven =
[propext, Classical.choice, Quot.sound]`, built on Mathlib `db127794`, one day from ours). The
master's lines 1–15806 are the Siegel–Walfisz master, ported separately as `Principia.Common.SW`
and not duplicated here. The master imported `Mathlib` and two PNT+ modules; here the imports are
narrowed, the namespace `GoldbachChain` is `Principia.Common.Goldbach`, and the one Siegel–Walfisz
input carries the SW port's hypothesis `MediumPNTBound` (see `Principia.Common.Goldbach.Reduction`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
open DirichletCharacter Complex PowerSeries ArithmeticFunction Finset Filter Metric MeasureTheory

namespace Principia.Common.Goldbach

-- ==== HOISTED shared definitions (single canonical copies) ====
open Finset

/-- `e(x) = exp(2πi x)`, the additive character of the circle. -/
noncomputable def e (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * x)

lemma e_norm (x : ℝ) : ‖e x‖ = 1 := by
  rw [e, Complex.norm_exp]
  have : (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [this, Real.exp_zero]

lemma e_pow (α : ℝ) (n : ℕ) : e (n * α) = (e α) ^ n := by
  rw [e, e, ← Complex.exp_nat_mul]
  congr 1
  push_cast; ring

lemma e_add (x y : ℝ) : e x * e y = e (x + y) := by
  rw [e, e, e, ← Complex.exp_add]; congr 1; push_cast; ring

lemma e_conj (x : ℝ) : (starRingEnd ℂ) (e x) = e (-x) := by
  rw [e, e, ← Complex.exp_conj]; congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
  push_cast; ring

lemma geom_exp_bound (z : ℂ) (hz : z ≠ 1) (hz1 : ‖z‖ = 1) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, z ^ n‖ ≤ 2 / ‖z - 1‖ := by
  have hzsub : (0 : ℝ) < ‖z - 1‖ := by
    rw [norm_pos_iff]; exact sub_ne_zero_of_ne hz
  rw [geom_sum_eq hz, norm_div]
  gcongr
  calc ‖z ^ N - 1‖ ≤ ‖z ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_pow, hz1]; norm_num

lemma e_sub_one_norm (α : ℝ) : ‖e α - 1‖ = 2 * |Real.sin (Real.pi * α)| := by
  have harg : e α = Complex.exp ((↑(2 * Real.pi * α) : ℂ) * Complex.I) := by
    rw [e]; congr 1; push_cast; ring
  have hre : (e α).re = Real.cos (2 * Real.pi * α) := by
    rw [harg]; exact Complex.exp_ofReal_mul_I_re _
  have him : (e α).im = Real.sin (2 * Real.pi * α) := by
    rw [harg]; exact Complex.exp_ofReal_mul_I_im _
  have e1 : Real.cos (2 * Real.pi * α) = 2 * Real.cos (Real.pi * α) ^ 2 - 1 := by
    rw [show 2 * Real.pi * α = 2 * (Real.pi * α) by ring]; exact Real.cos_two_mul _
  have e2 : Real.sin (2 * Real.pi * α)
      = 2 * Real.sin (Real.pi * α) * Real.cos (Real.pi * α) := by
    rw [show 2 * Real.pi * α = 2 * (Real.pi * α) by ring]; exact Real.sin_two_mul _
  have hnn : (0 : ℝ) ≤ 2 * |Real.sin (Real.pi * α)| := by positivity
  rw [← Real.sqrt_sq (norm_nonneg (e α - 1)), ← Real.sqrt_sq hnn]
  congr 1
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, hre, him]
  rw [e1, e2, mul_pow, sq_abs]
  nlinarith [Real.sin_sq_add_cos_sq (Real.pi * α)]

lemma exp_sum_le_sin (α : ℝ) (hα : Real.sin (Real.pi * α) ≠ 0) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, e (n * α)‖ ≤ 1 / |Real.sin (Real.pi * α)| := by
  have hne : e α ≠ 1 := by
    intro h
    have h0 : ‖e α - 1‖ = 2 * |Real.sin (Real.pi * α)| := e_sub_one_norm α
    rw [h, sub_self, norm_zero] at h0
    have : |Real.sin (Real.pi * α)| = 0 := by linarith [abs_nonneg (Real.sin (Real.pi * α))]
    exact hα (abs_eq_zero.mp this)
  have hsum : ∑ n ∈ Finset.range N, e (n * α) = ∑ n ∈ Finset.range N, (e α) ^ n :=
    Finset.sum_congr rfl (fun n _ => e_pow α n)
  have key : ‖∑ n ∈ Finset.range N, e (n * α)‖ ≤ 2 / ‖e α - 1‖ := by
    rw [hsum]; exact geom_exp_bound (e α) hne (e_norm α) N
  rw [e_sub_one_norm α] at key
  have habs : (0 : ℝ) < |Real.sin (Real.pi * α)| := abs_pos.mpr hα
  calc ‖∑ n ∈ Finset.range N, e (n * α)‖ ≤ 2 / (2 * |Real.sin (Real.pi * α)|) := key
    _ = 1 / |Real.sin (Real.pi * α)| := by rw [div_mul_eq_div_div]; norm_num

lemma two_dist_le_abs_sin (α : ℝ) : 2 * |α - round α| ≤ |Real.sin (Real.pi * α)| := by
  set m : ℤ := round α with hm
  set r : ℝ := α - (m : ℝ) with hr
  have hrabs : |r| ≤ 1 / 2 := by rw [hr]; exact abs_sub_round α
  have hαsplit : Real.pi * α = Real.pi * r + (m : ℝ) * Real.pi := by
    rw [hr]; ring
  have hsin : Real.sin (Real.pi * α) = (-1) ^ m * Real.sin (Real.pi * r) := by
    rw [hαsplit, Real.sin_add_int_mul_pi]
  have habs1 : |Real.sin (Real.pi * α)| = |Real.sin (Real.pi * r)| := by
    rw [hsin, abs_mul, abs_zpow, abs_neg, abs_one, one_zpow, one_mul]
  have hpr : |Real.sin (Real.pi * r)| = Real.sin (Real.pi * |r|) := by
    by_cases hrpos : 0 ≤ r
    · rw [abs_of_nonneg hrpos,
        abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by positivity)
          (by nlinarith [Real.pi_pos, (abs_le.mp hrabs).2]))]
    · replace hrpos : r < 0 := not_le.mp hrpos
      have hle0 : Real.sin (Real.pi * r) ≤ 0 := by
        have h1 : 0 ≤ Real.sin (Real.pi * (-r)) :=
          Real.sin_nonneg_of_nonneg_of_le_pi (by nlinarith [Real.pi_pos])
            (by nlinarith [Real.pi_pos, (abs_le.mp hrabs).1])
        rw [show Real.pi * (-r) = -(Real.pi * r) by ring, Real.sin_neg] at h1
        linarith
      rw [abs_of_neg hrpos, abs_of_nonpos hle0,
        show Real.pi * -r = -(Real.pi * r) by ring, Real.sin_neg]
  have hjordan : 2 * |r| ≤ Real.sin (Real.pi * |r|) := by
    have hj := Real.le_sin_mul (x := 2 * |r|) (by positivity) (by nlinarith [hrabs])
    rwa [show Real.pi / 2 * (2 * |r|) = Real.pi * |r| by ring] at hj
  calc 2 * |α - round α| = 2 * |r| := by rw [hr]
    _ ≤ Real.sin (Real.pi * |r|) := hjordan
    _ = |Real.sin (Real.pi * r)| := hpr.symm
    _ = |Real.sin (Real.pi * α)| := habs1.symm

lemma exp_sum_bound (α : ℝ) (hα : Real.sin (Real.pi * α) ≠ 0) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, e (n * α)‖ ≤ 1 / (2 * |α - round α|) := by
  have h2 := two_dist_le_abs_sin α
  have hd : (0 : ℝ) < 2 * |α - round α| := by
    rcases (abs_nonneg (α - (round α : ℝ))).lt_or_eq with h | h
    · positivity
    · exfalso; apply hα
      have hz : α - (round α : ℝ) = 0 := abs_eq_zero.mp h.symm
      have hαeq : α = (round α : ℝ) := by linarith
      rw [hαeq, show Real.pi * (round α : ℝ) = (round α : ℝ) * Real.pi by ring,
        Real.sin_int_mul_pi]
  exact le_trans (exp_sum_le_sin α hα N) (one_div_le_one_div_of_le hd h2)

lemma exp_sum_trivial (α : ℝ) (N : ℕ) : ‖∑ n ∈ Finset.range N, e (n * α)‖ ≤ N := by
  calc ‖∑ n ∈ Finset.range N, e (n * α)‖
      ≤ ∑ n ∈ Finset.range N, ‖e (n * α)‖ := norm_sum_le _ _
    _ = N := by simp [e_norm]

/-- The capped exponential-sum bound in workhorse-weight form:
    `‖∑_{n<M} e(nβ)‖ ≤ [if β∈ℤ then M else min(M, 1/(2‖β‖))]`. -/
lemma exp_sum_min_bound (β : ℝ) (M : ℕ) :
    ‖∑ n ∈ Finset.range M, e (n * β)‖
      ≤ (if β - round β = 0 then (M : ℝ)
         else min (M : ℝ) (1 / (2 * |β - round β|))) := by
  split
  · exact exp_sum_trivial β M
  · rename_i hne
    apply le_min (exp_sum_trivial β M)
    have hsin : Real.sin (Real.pi * β) ≠ 0 := by
      intro h0
      apply hne
      rw [Real.sin_eq_zero_iff] at h0
      obtain ⟨n, hn⟩ := h0
      have h2 : Real.pi * (n : ℝ) = Real.pi * β := by linear_combination hn
      have hβ : β = (n : ℝ) := (mul_left_cancel₀ Real.pi_ne_zero h2).symm
      rw [hβ, round_intCast]
      ring
    exact exp_sum_bound β hsin M

/-- `e(α) = 1` iff `α` is an integer. -/
lemma e_eq_one_iff (α : ℝ) : e α = 1 ↔ ∃ k : ℤ, α = (k : ℝ) := by
  rw [e, Complex.exp_eq_one_iff]
  have h2πI : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [mul_comm ((k : ℤ) : ℂ) (2 * (Real.pi : ℂ) * Complex.I)] at hk
    exact_mod_cast mul_left_cancel₀ h2πI hk
  · rintro ⟨k, rfl⟩
    exact ⟨k, by push_cast; ring⟩

open Filter in
/-- The arithmetic model coefficients for `Λ` mod `q`: `1/φ(q)` on units, `0` off. -/
noncomputable def lambdaModel (q : ℕ) : ℕ → ℂ :=
  fun r => if Nat.gcd r q = 1 then 1 / (Nat.totient q : ℂ) else 0

/-- **The major arcs**: the union of the Farey windows `|α − a/q| ≤ 1/(q(Q+1))` over
    moduli `q ≤ P`. Countable union of closed balls, hence measurable. -/
def MajorArcs (P Q : ℕ) : Set ℝ :=
  ⋃ q ∈ Set.Icc 1 P, ⋃ a : ℤ, Metric.closedBall ((a : ℝ) / q) (1 / (q * (Q + 1)))

/-- The finite set of REDUCED Farey anchors with moduli ≤ P relevant to `(0,1]`. -/
noncomputable def anchors (P : ℕ) : Finset (ℕ × ℤ) :=
  (Finset.Icc 1 P ×ˢ Finset.Icc (-(P : ℤ)) (2 * P)).filter
    (fun pq => Int.gcd pq.2 pq.1 = 1)

noncomputable def minorCsup (N U V P Q : ℕ) : ℝ :=
  2 * Real.log (N + 1) * ((2 * (N : ℝ) / P) * (1 + Real.log U)
      + (16 * U + 4 * Q) * (2 + Real.log (2 * Q)) + U)
  + Real.log (U * V) * ((2 * (N : ℝ) / P) * (1 + Real.log (U * V))
      + (16 * (U * V) + 4 * Q) * (2 + Real.log (2 * Q)))
  + (V : ℝ) * Real.log V
  + Real.log N * (4 * Real.sqrt 10 * N / Real.sqrt (V + 1)
      + Real.sqrt 32 * N * ((Nat.log 2 N + 1 : ℕ) : ℝ) / Real.sqrt P
      + 64 * N * Real.sqrt (1 + Real.log (2 * Q)) / Real.sqrt U
      + 6 * ((Nat.log 2 N + 1 : ℕ) : ℝ) * Real.sqrt (N * Q * (1 + Real.log (2 * Q))))

set_option maxHeartbeats 1000000

/-!
# The Vinogradov minor-arc sup bound for `∑ Λ(n) e(nα)` — the complete chain

**Main theorem** (`MinSum.vinogradov_sup`): for `gcd(a,q) = 1`, `|α − a/q| ≤ 1/q²`,
`q ≥ 2`, `U ≤ N`, `1 ≤ U·V ≤ N`:

  `‖∑_{n≤N} Λ(n) e(nα)‖ ≤ B₁(U,N,q) + B₂(UV,N,q) + V·log V + B₄(U,N,q)`

with every `Bᵢ` fully explicit — the analytic heart of the circle method's minor arcs
for almost-all binary Goldbach (`AlmostAllGoldbachReduction.lean` consumes the variance
bound this sup feeds). Built entirely from Mathlib, self-contained in this file.

The chain, bottom to top (every lemma verified 0 errors / 0 sorries with
`#print axioms` = `[propext, Classical.choice, Quot.sound]`):

## 1. The min-sum workhorse (Vaughan Lemma 2.2 / IK 13.7)
  • `image_natCast_Ico`, `image_mul_natCast_Ico` — block bijections onto `ZMod q`.
  • `sum_Icc_reflect`, `sum_one_div_le`, `sum_q_div_min_le` — the harmonic core.
  • `dist_round_le` (1-Lipschitz), `dist_round_neg` (even), `dist_int_div_ge` (q∤m separation).
  • `spaced_floor_sign_injOn`, `spaced_min_sum_le` — the δ-spaced counting core
    (`∑ min(V, 1/(2·dist)) ≤ 2V + (2/δ)(1+log(1/δ))`).
  • `block_spaced` — `L ≤ q/2` consecutive `h` make `hα` pairwise `1/(2q)`-spaced.
  • `range_min_sum_le` — **the workhorse, uniform-cap form**:
    `∑_{h∈[M,M+R)} min(V, 1/(2‖hα‖)) ≤ (R/(q/2)+1)(2V + 4q(1+log 2q))`.
  • `dyadic_cap_sum_le` — **the N/h-cap form** via dyadic blocks:
    `∑_{h≤H} min(N/h, 1/(2‖hα‖)) ≤ (log₂H+1)(8N/q + 4qL) + 32HL + 4N`.
  • `cap_symmetric_sum_le` — the symmetric-in-h pure-cap form.

## 2. The exponential-sum chain (self-contained copy of the `MinorArcExpSum.lean` core)
  • `e`, `e_norm`, `e_pow`, `e_add`, `e_conj`; `geom_exp_bound`, `e_sub_one_norm`,
    `exp_sum_le_sin`, `two_dist_le_abs_sin`, `exp_sum_bound`, `exp_sum_trivial`.
  • `exp_sum_min_bound`, `exp_sum_Ico_min_bound`, `exp_sum_Ioc_min_bound` — capped forms.
  • `abel_exp_sum` — monotone weights cost only `2W` (partial summation).

## 3. Type I / Type II
  • `typeI_sum_bound` — `∑_{d≤D} ‖∑_{n<M} e(ndα)‖ ≤ (D/(q/2)+1)(2M + 4qL)`.
  • `typeII_second_moment_le`, `dist_round_neg`, `diff_count_le`, `typeII_h_sum_le`,
    `typeII_second_moment_workhorse`, `typeII_bilinear_sq_le` — the bilinear estimate.

## 4. The Vaughan combine (section `VaughanDecomposition`)
  • `vaughan_identity` (ring form), `vaughan_sum_decomposition` — `∑Λe = S₁−S₂+S₃+S₄`.
  • `sum_Ioc_mul_weight`, `sum_Ioc_mul_weight_eq_sum_sum` — the weighted hyperbola
    unfolding and regrouping (`∑(f∗g)(n)w(n) = ∑_d f(d)∑_{m≤N/d} g(m)w(dm)`).
  • `truncate` + `abs_truncate_moebius_le_one`, `truncate_vonMangoldt_nonneg/le`,
    `abs_truncate_mul_le_log`, `truncate_mul_eq_zero_of_gt`, `sum_vonMangoldt_le`,
    `sum_Ioc_zeta_mul`, `log_natCast_nonneg/monotone`, `cap_succ_le`, `sub_apply'`,
    `tail_conv_nonneg/le_log/eq_zero_of_le`, `moebius_tail_eq_zero_of_le`,
    `abs_moebius_tail_le_one` — the truncated Vaughan pieces with all sup/support facts.
  • `filtered_exp_sum_cap`, `hyperbola_second_moment_expand`, `S4_block_second_moment`
    — the hyperbola problem (varying `m ≤ N/d` ranges), solved.
  • **`S1_bound`, `S2_bound`, `S3_bound`, `S4_bound`** — the four Vaughan pieces,
    each explicitly bounded on the arc.
  • `vinogradov_sup_skeleton`, **`vinogradov_sup`** — the final composition.

Pinned: `leanprover/lean4:v4.31.0` + Mathlib v4.31.0. Companion files:
`MinorArcExpSum.lean` (exp-sum core + Parseval + char orthogonality),
`VaughanIdentity.lean`, `AlmostAllGoldbachReduction.lean`.
-/

namespace MinSum

open Finset

/-- Any `q` consecutive naturals cast onto `ZMod q` bijectively (as a Finset image). -/
lemma image_natCast_Ico (q : ℕ) [NeZero q] (M : ℕ) :
    Finset.image (fun h : ℕ => (h : ZMod q)) (Finset.Ico M (M + q)) = Finset.univ := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hinj : Set.InjOn (fun h : ℕ => (h : ZMod q)) (Finset.Ico M (M + q)) := by
    intro x hx y hy hxy
    simp only [Finset.coe_Ico, Set.mem_Ico] at hx hy
    have hmod : x ≡ y [MOD q] := (ZMod.natCast_eq_natCast_iff x y q).mp hxy
    have hdvd : (q : ℤ) ∣ (y : ℤ) - x := hmod.dvd
    have hlt : |(y : ℤ) - x| < q := by
      rw [abs_lt]
      constructor <;> [skip; skip] <;> omega
    have : (y : ℤ) - x = 0 := Int.eq_zero_of_abs_lt_dvd hdvd hlt
    omega
  have hcard : (Finset.image (fun h : ℕ => (h : ZMod q)) (Finset.Ico M (M + q))).card
      = Finset.univ.card (α := ZMod q) := by
    rw [Finset.card_image_of_injOn hinj, Nat.card_Ico]
    simp [ZMod.card q]
  exact Finset.eq_univ_of_card _ hcard

/-- With `gcd(a,q) = 1`, the map `h ↦ h·a` on any `q` consecutive naturals covers `ZMod q`. -/
lemma image_mul_natCast_Ico (q : ℕ) [NeZero q] (a : ℕ) (ha : Nat.Coprime a q) (M : ℕ) :
    Finset.image (fun h : ℕ => (h : ZMod q) * a) (Finset.Ico M (M + q)) = Finset.univ := by
  have h1 : Finset.image (fun h : ℕ => (h : ZMod q) * a) (Finset.Ico M (M + q))
      = Finset.image (fun x : ZMod q => x * a)
          (Finset.image (fun h : ℕ => (h : ZMod q)) (Finset.Ico M (M + q))) := by
    rw [Finset.image_image]; rfl
  rw [h1, image_natCast_Ico q M]
  have hunit : IsUnit ((a : ZMod q)) := (ZMod.isUnit_iff_coprime a q).mpr ha
  obtain ⟨u, hu⟩ := hunit
  apply Finset.image_univ_of_surjective
  intro x
  refine ⟨x * ↑u⁻¹, ?_⟩
  show x * ↑u⁻¹ * (a : ZMod q) = x
  rw [← hu, mul_assoc, Units.inv_mul, mul_one]

/-- `dist(·,ℤ)` is 1-Lipschitz: `‖x‖ ≤ |x−y| + ‖y‖` (round minimizes over ℤ).
    This is the perturbation step: for `|α − a/q| ≤ 1/q²` it transfers the `‖h·a/q‖`
    block counting to `‖hα‖` at the cost of `h/q² ≤ 1/q` per block. -/
lemma dist_round_le (x y : ℝ) :
    |x - round x| ≤ |x - y| + |y - round y| := by
  calc |x - round x| ≤ |x - round y| := round_le x (round y)
    _ = |(x - y) + (y - round y)| := by ring_nf
    _ ≤ |x - y| + |y - round y| := abs_add_le _ _

/-- A rational `m/q` with `q ∤ m` is at distance `≥ 1/q` from every integer.
    (Feeds the block-spacing fact: `(h₁−h₂)·a/q` is `1/q`-separated from ℤ when
    `q ∤ (h₁−h₂)a`, which the coprime block bijection guarantees.) -/
lemma dist_int_div_ge (m : ℤ) (q : ℕ) (hq : 0 < q) (hnd : ¬ (q : ℤ) ∣ m) :
    1 / (q : ℝ) ≤ |(m : ℝ) / q - round ((m : ℝ) / q)| := by
  set r : ℤ := m - q * round ((m : ℝ) / q) with hr
  have hrne : r ≠ 0 := by
    intro h
    apply hnd
    refine ⟨round ((m : ℝ) / q), ?_⟩
    omega
  have h1 : (1 : ℤ) ≤ |r| := Int.one_le_abs hrne
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have heq : (m : ℝ) / q - round ((m : ℝ) / q) = (r : ℝ) / q := by
    rw [hr]
    push_cast
    field_simp
  rw [heq, abs_div, abs_of_nonneg hqR.le]
  gcongr
  · exact_mod_cast h1

/-- Reflection: `∑_{k=1}^{q-1} f(q-k) = ∑_{k=1}^{q-1} f(k)`. -/
lemma sum_Icc_reflect (q : ℕ) (f : ℕ → ℝ) :
    ∑ k ∈ Finset.Icc 1 (q - 1), f (q - k) = ∑ k ∈ Finset.Icc 1 (q - 1), f k := by
  apply Finset.sum_nbij' (i := fun k => q - k) (j := fun k => q - k)
  · intro k hk; simp only [Finset.mem_Icc] at *; omega
  · intro k hk; simp only [Finset.mem_Icc] at *; omega
  · intro k hk; simp only [Finset.mem_Icc] at hk; omega
  · intro k hk; simp only [Finset.mem_Icc] at hk; omega
  · intro k hk; rfl

/-- Harmonic-sum form: `∑_{k=1}^{n} 1/k ≤ 1 + log n`. -/
lemma sum_one_div_le (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / k ≤ 1 + Real.log n := by
  have h1 : ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / k = ((harmonic n : ℚ) : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    simp [one_div]
  rw [h1]
  exact harmonic_le_one_add_log n

/-- **The harmonic core of the min-sum workhorse**:
    `∑_{k=1}^{q-1} q / min(k, q-k) ≤ 2q(1 + log q)`. Since `‖k/q‖ = min(k, q-k)/q`,
    this is exactly `∑_{k≠0 mod q} 1/(2‖k/q‖) ≤ 4q(1+log q)`-strength — the per-block
    contribution of the non-exceptional residues. -/
lemma sum_q_div_min_le (q : ℕ) (hq : 1 ≤ q) :
    ∑ k ∈ Finset.Icc 1 (q - 1), (q : ℝ) / ((min k (q - k) : ℕ) : ℝ)
      ≤ 2 * q * (1 + Real.log q) := by
  have hlogq : 0 ≤ Real.log q := by
    rcases Nat.eq_or_lt_of_le hq with h | h
    · rw [← h]; simp
    · exact Real.log_nonneg (by exact_mod_cast h.le)
  have step1 : ∀ k ∈ Finset.Icc 1 (q - 1),
      (q : ℝ) / ((min k (q - k) : ℕ) : ℝ) ≤ (q : ℝ) / k + (q : ℝ) / ((q - k : ℕ) : ℝ) := by
    intro k hk
    simp only [Finset.mem_Icc] at hk
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk.1
    have hqk : 1 ≤ q - k := by omega
    have hqk1 : (1 : ℝ) ≤ ((q - k : ℕ) : ℝ) := by exact_mod_cast hqk
    have hposk : (0 : ℝ) < (k : ℝ) := by linarith
    have hposqk : (0 : ℝ) < ((q - k : ℕ) : ℝ) := by linarith
    rcases min_choice k (q - k) with h | h <;> rw [h]
    · have h2 : (0 : ℝ) ≤ (q : ℝ) / ((q - k : ℕ) : ℝ) := by positivity
      linarith
    · have h2 : (0 : ℝ) ≤ (q : ℝ) / (k : ℝ) := by positivity
      linarith
  have hrefl : ∑ k ∈ Finset.Icc 1 (q - 1), (q : ℝ) / ((q - k : ℕ) : ℝ)
      = ∑ k ∈ Finset.Icc 1 (q - 1), (q : ℝ) / (k : ℝ) :=
    sum_Icc_reflect q (fun k => (q : ℝ) / (k : ℝ))
  have hharm : ∑ k ∈ Finset.Icc 1 (q - 1), (q : ℝ) / (k : ℝ)
      ≤ (q : ℝ) * (1 + Real.log q) := by
    have h1 : ∑ k ∈ Finset.Icc 1 (q - 1), (q : ℝ) / (k : ℝ)
        = (q : ℝ) * ∑ k ∈ Finset.Icc 1 (q - 1), (1 : ℝ) / k := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun k _ => by rw [div_eq_mul_inv, one_div])
    rw [h1]
    have h2 : ∑ k ∈ Finset.Icc 1 (q - 1), (1 : ℝ) / k ≤ 1 + Real.log (q - 1 : ℕ) :=
      sum_one_div_le (q - 1)
    have h3 : Real.log ((q - 1 : ℕ) : ℝ) ≤ Real.log q := by
      rcases Nat.eq_or_lt_of_le hq with h | h
      · rw [← h]; simp
      · apply Real.log_le_log (by exact_mod_cast Nat.sub_pos_of_lt h)
        have : q - 1 ≤ q := Nat.sub_le q 1
        exact_mod_cast this
    have hq0 : (0 : ℝ) ≤ (q : ℝ) := by positivity
    nlinarith [h2, h3]
  calc ∑ k ∈ Finset.Icc 1 (q - 1), (q : ℝ) / ((min k (q - k) : ℕ) : ℝ)
      ≤ ∑ k ∈ Finset.Icc 1 (q - 1), ((q : ℝ) / k + (q : ℝ) / ((q - k : ℕ) : ℝ)) :=
        Finset.sum_le_sum step1
    _ = ∑ k ∈ Finset.Icc 1 (q - 1), (q : ℝ) / (k : ℝ)
        + ∑ k ∈ Finset.Icc 1 (q - 1), (q : ℝ) / ((q - k : ℕ) : ℝ) := Finset.sum_add_distrib
    _ = 2 * ∑ k ∈ Finset.Icc 1 (q - 1), (q : ℝ) / (k : ℝ) := by rw [hrefl]; ring
    _ ≤ 2 * ((q : ℝ) * (1 + Real.log q)) := by linarith [hharm]
    _ = 2 * q * (1 + Real.log q) := by ring

/-- **Spacing injection** (the counting core of the min-sum workhorse / baby large sieve):
    if the points `x i` are pairwise `δ`-spaced mod 1, then the map
    `i ↦ (⌊2·dist(xᵢ,ℤ)/δ⌋, sign of the signed distance)` is injective — i.e. each
    distance-annulus `[kδ/2, (k+1)δ/2)` holds at most one point on each side of ℤ. -/
lemma spaced_floor_sign_injOn {ι : Type*} (s : Finset ι) (x : ι → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hspace : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ |(x i - x j) - round (x i - x j)|) :
    Set.InjOn (fun i =>
      ((⌊2 * |x i - round (x i)| / δ⌋₊, decide (0 ≤ x i - round (x i))) : ℕ × Bool))
      (s : Set ι) := by
  intro i hi j hj hij
  by_contra hne
  have hsp := hspace i hi j hj hne
  set fi : ℝ := x i - round (x i) with hfi
  set fj : ℝ := x j - round (x j) with hfj
  have hk : ⌊2 * |fi| / δ⌋₊ = ⌊2 * |fj| / δ⌋₊ := by
    have := congrArg Prod.fst hij; simpa using this
  have hb : (0 ≤ fi) ↔ (0 ≤ fj) := by
    have := congrArg Prod.snd hij
    simp only [decide_eq_decide] at this
    exact this
  -- floor equality ⇒ ||fi| − |fj|| < δ/2
  have ha0 : 0 ≤ 2 * |fi| / δ := by positivity
  have hb0 : 0 ≤ 2 * |fj| / δ := by positivity
  have habs : |(|fi| - |fj|)| < δ / 2 := by
    have h1 : 2 * |fi| / δ < ⌊2 * |fi| / δ⌋₊ + 1 := Nat.lt_floor_add_one _
    have h2 : (⌊2 * |fj| / δ⌋₊ : ℝ) ≤ 2 * |fj| / δ := Nat.floor_le hb0
    have h3 : 2 * |fj| / δ < ⌊2 * |fj| / δ⌋₊ + 1 := Nat.lt_floor_add_one _
    have h4 : (⌊2 * |fi| / δ⌋₊ : ℝ) ≤ 2 * |fi| / δ := Nat.floor_le ha0
    rw [hk] at h1 h4
    have hd1 : 2 * |fi| / δ - 2 * |fj| / δ < 1 := by linarith
    have hd2 : 2 * |fj| / δ - 2 * |fi| / δ < 1 := by linarith
    have hd1' : 2 * |fi| - 2 * |fj| < δ :=
      (div_lt_one hδ).mp (by rw [sub_div]; linarith [hd1])
    have hd2' : 2 * |fj| - 2 * |fi| < δ :=
      (div_lt_one hδ).mp (by rw [sub_div]; linarith [hd2])
    rw [abs_lt]
    constructor <;> linarith
  -- same sign ⇒ |fi − fj| = ||fi| − |fj|| < δ
  have hsame : |fi - fj| < δ := by
    by_cases hpos : 0 ≤ fi
    · have hpj : 0 ≤ fj := hb.mp hpos
      calc |fi - fj| = |(|fi| - |fj|)| := by rw [abs_of_nonneg hpos, abs_of_nonneg hpj]
        _ < δ / 2 := habs
        _ < δ := by linarith
    · have hneg : fi < 0 := not_le.mp hpos
      have hnj : fj < 0 := by
        by_contra hc
        exact absurd (hb.mpr (not_lt.mp hc)) hpos
      calc |fi - fj| = |(|fi| - |fj|)| := by
            rw [abs_of_neg hneg, abs_of_neg hnj, ← abs_neg]; ring_nf
        _ < δ / 2 := habs
        _ < δ := by linarith
  -- dist(xᵢ−xⱼ, ℤ) ≤ |fi − fj| (round minimizes), contradicting the spacing
  have hmin : |(x i - x j) - round (x i - x j)| ≤ |fi - fj| := by
    have heq : fi - fj = (x i - x j) - ((round (x i) - round (x j) : ℤ) : ℝ) := by
      push_cast; rw [hfi, hfj]; ring
    calc |(x i - x j) - round (x i - x j)|
        ≤ |(x i - x j) - ((round (x i) - round (x j) : ℤ) : ℝ)| :=
          round_le (x i - x j) (round (x i) - round (x j))
      _ = |fi - fj| := by rw [heq]
  linarith

/-- **Spaced-points min-sum bound** (the workhorse's per-block estimate): pairwise
    δ-spaced points contribute at most `2V + (2/δ)(1 + log(1/δ))` to the capped
    reciprocal-distance sum. Combines the spacing injection with the harmonic bound. -/
lemma spaced_min_sum_le {ι : Type*} (s : Finset ι) (x : ι → ℝ) (δ V : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hV : 0 ≤ V)
    (hspace : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ |(x i - x j) - round (x i - x j)|) :
    ∑ i ∈ s, (if x i - round (x i) = 0 then V
              else min V (1 / (2 * |x i - round (x i)|)))
      ≤ 2 * V + (2 / δ) * (1 + Real.log (1 / δ)) := by
  classical
  set K : ℕ := ⌊1 / δ⌋₊ with hK
  set φ : ι → ℕ × Bool := fun i =>
    (⌊2 * |x i - round (x i)| / δ⌋₊, decide (0 ≤ x i - round (x i))) with hφ
  set W : ℕ × Bool → ℝ := fun p => if p.1 = 0 then V else 1 / (p.1 * δ) with hW
  have hW0 : ∀ p, 0 ≤ W p := by
    intro p
    rw [hW]
    dsimp only
    split
    · exact hV
    · rename_i h
      have hp : (0 : ℝ) < p.1 := by exact_mod_cast Nat.pos_of_ne_zero h
      positivity
  -- termwise: each term is at most W (φ i)
  have hterm : ∀ i ∈ s, (if x i - round (x i) = 0 then V
      else min V (1 / (2 * |x i - round (x i)|))) ≤ W (φ i) := by
    intro i _
    by_cases hf0 : x i - round (x i) = 0
    · rw [if_pos hf0, hW, hφ]
      dsimp only
      rw [hf0]
      simp
    · rw [if_neg hf0]
      by_cases hk : ⌊2 * |x i - round (x i)| / δ⌋₊ = 0
      · have : W (φ i) = V := by rw [hW, hφ]; dsimp only; rw [if_pos hk]
        rw [this]
        exact min_le_left _ _
      · have habs : 0 < |x i - round (x i)| := abs_pos.mpr hf0
        have hkle : (⌊2 * |x i - round (x i)| / δ⌋₊ : ℝ)
            ≤ 2 * |x i - round (x i)| / δ := Nat.floor_le (by positivity)
        have h1 : (⌊2 * |x i - round (x i)| / δ⌋₊ : ℝ) * δ ≤ 2 * |x i - round (x i)| := by
          have := mul_le_mul_of_nonneg_right hkle hδ.le
          rwa [div_mul_cancel₀ _ (ne_of_gt hδ)] at this
        have hkpos : (0 : ℝ) < (⌊2 * |x i - round (x i)| / δ⌋₊ : ℝ) := by
          exact_mod_cast Nat.pos_of_ne_zero hk
        have h2 : 1 / (2 * |x i - round (x i)|)
            ≤ 1 / ((⌊2 * |x i - round (x i)| / δ⌋₊ : ℝ) * δ) :=
          one_div_le_one_div_of_le (by positivity) h1
        have h3 : W (φ i) = 1 / ((⌊2 * |x i - round (x i)| / δ⌋₊ : ℝ) * δ) := by
          rw [hW, hφ]; dsimp only; rw [if_neg hk]
        rw [h3]
        exact le_trans (min_le_right _ _) h2
  -- image is inside range (K+1) ×ˢ Bool
  have himg : s.image φ ⊆ (Finset.range (K + 1)) ×ˢ (Finset.univ : Finset Bool) := by
    intro p hp
    simp only [Finset.mem_image] at hp
    obtain ⟨i, _, rfl⟩ := hp
    rw [Finset.mem_product]
    refine ⟨?_, Finset.mem_univ _⟩
    rw [Finset.mem_range, Nat.lt_succ_iff, hK]
    apply Nat.floor_mono
    have hhalf : |x i - round (x i)| ≤ 1 / 2 := abs_sub_round (x i)
    have : 2 * |x i - round (x i)| ≤ 1 := by linarith
    exact div_le_div_of_nonneg_right this hδ.le
  -- assemble
  calc ∑ i ∈ s, (if x i - round (x i) = 0 then V
        else min V (1 / (2 * |x i - round (x i)|)))
      ≤ ∑ i ∈ s, W (φ i) := Finset.sum_le_sum hterm
    _ = ∑ p ∈ s.image φ, W p := by
        rw [Finset.sum_image]
        intro a ha b hb hab
        exact spaced_floor_sign_injOn s x δ hδ hspace ha hb hab
    _ ≤ ∑ p ∈ (Finset.range (K + 1)) ×ˢ (Finset.univ : Finset Bool), W p :=
        Finset.sum_le_sum_of_subset_of_nonneg himg (fun p _ _ => hW0 p)
    _ = ∑ k ∈ Finset.range (K + 1), ∑ b : Bool, W (k, b) := by rw [Finset.sum_product]
    _ = ∑ k ∈ Finset.range (K + 1), 2 * (if k = 0 then V else 1 / (k * δ)) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [Fintype.sum_bool, hW]
        dsimp only
        ring
    _ = 2 * V + 2 * ∑ k ∈ Finset.Icc 1 K, 1 / ((k : ℝ) * δ) := by
        have hsplit : Finset.range (K + 1) = insert 0 (Finset.Icc 1 K) := by
          ext k
          simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
          omega
        rw [hsplit, Finset.sum_insert (by simp)]
        rw [if_pos rfl]
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        simp only [Finset.mem_Icc] at hk
        rw [if_neg (by omega)]
    _ ≤ 2 * V + (2 / δ) * (1 + Real.log (1 / δ)) := by
        have hδinv : (0 : ℝ) < 1 / δ := by positivity
        have hKle : (K : ℝ) ≤ 1 / δ := by
          rw [hK]; exact Nat.floor_le hδinv.le
        have hK1 : 1 ≤ K := by
          rw [hK]
          apply Nat.le_floor
          rw [Nat.cast_one]
          rw [le_div_iff₀ hδ]
          linarith
        have h1 : ∑ k ∈ Finset.Icc 1 K, 1 / ((k : ℝ) * δ)
            = (1 / δ) * ∑ k ∈ Finset.Icc 1 K, (1 : ℝ) / k := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k hk
          simp only [Finset.mem_Icc] at hk
          have : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk.1
          field_simp
        have h2 := sum_one_div_le K
        have h3 : Real.log K ≤ Real.log (1 / δ) := by
          apply Real.log_le_log (by exact_mod_cast hK1) hKle
        have hlog0 : 0 ≤ Real.log (1 / δ) := by
          apply Real.log_nonneg
          rw [le_div_iff₀ hδ]
          linarith
        rw [h1]
        have h4 : ∑ k ∈ Finset.Icc 1 K, (1 : ℝ) / k ≤ 1 + Real.log (1 / δ) := by linarith
        have h5 : (1 / δ) * ∑ k ∈ Finset.Icc 1 K, (1 : ℝ) / k
            ≤ (1 / δ) * (1 + Real.log (1 / δ)) := by
          apply mul_le_mul_of_nonneg_left h4 hδinv.le
        have h6 : (2 : ℝ) / δ = 2 * (1 / δ) := by ring
        rw [h6]
        linarith

/-- **Block spacing**: for `gcd(a,q)=1` and `|α − a/q| ≤ 1/q²`, the points `hα` for `h`
    in a run of `L ≤ q/2` consecutive integers are pairwise `1/(2q)`-spaced mod 1.
    (So each such block feeds `spaced_min_sum_le` with `δ = 1/(2q)`.) -/
lemma block_spaced (a q : ℕ) (hq : 0 < q) (ha : Nat.Coprime a q) (α : ℝ)
    (hα : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (M L : ℕ) (hL : 2 * L ≤ q) :
    ∀ i ∈ Finset.Ico M (M + L), ∀ j ∈ Finset.Ico M (M + L), i ≠ j →
      1 / (2 * (q : ℝ)) ≤
        |((i : ℝ) * α - (j : ℝ) * α) - round ((i : ℝ) * α - (j : ℝ) * α)| := by
  intro i hi j hj hij
  simp only [Finset.mem_Ico] at hi hj
  set d : ℤ := (i : ℤ) - j with hd
  have hdne : d ≠ 0 := by rw [hd]; omega
  have hdabs : |d| ≤ (L : ℤ) := abs_le.mpr ⟨by omega, by omega⟩
  -- q ∤ d·a (coprimality + |d| < q)
  have hnd : ¬ (q : ℤ) ∣ d * a := by
    intro hdvd
    have hu : IsUnit ((a : ZMod q)) := (ZMod.isUnit_iff_coprime a q).mpr ha
    have h0 : ((d * (a : ℤ) : ℤ) : ZMod q) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mpr hdvd
    push_cast at h0
    have hd0 : ((d : ℤ) : ZMod q) = 0 := (hu.mul_left_eq_zero).mp h0
    have hqd : (q : ℤ) ∣ d := (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp hd0
    have hqle : (q : ℤ) ≤ |d| := Int.le_of_dvd (abs_pos.mpr hdne) ((dvd_abs _ _).mpr hqd)
    have : (q : ℤ) ≤ (L : ℤ) := le_trans hqle hdabs
    omega
  -- the rational point d·a/q is 1/q-separated from ℤ
  have hsep : 1 / (q : ℝ) ≤ |((d * a : ℤ) : ℝ) / q - round (((d * a : ℤ) : ℝ) / q)| :=
    dist_int_div_ge (d * a) q hq hnd
  -- the perturbation |(iα−jα) − d·a/q| = |d|·|α−a/q| ≤ L/q² ≤ 1/(2q)
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hpert : |((i : ℝ) * α - (j : ℝ) * α) - ((d * a : ℤ) : ℝ) / q| ≤ 1 / (2 * (q : ℝ)) := by
    have h1 : (i : ℝ) * α - (j : ℝ) * α = (d : ℝ) * α := by
      rw [hd]; push_cast; ring
    have h2 : ((d * a : ℤ) : ℝ) / q = (d : ℝ) * ((a : ℝ) / q) := by
      push_cast; ring
    rw [h1, h2, ← mul_sub, abs_mul]
    have h3 : |(d : ℝ)| ≤ (L : ℝ) := by
      rw [← Int.cast_abs]
      exact_mod_cast hdabs
    have hL' : (2 : ℝ) * L ≤ q := by exact_mod_cast hL
    calc |(d : ℝ)| * |α - (a : ℝ) / q| ≤ (L : ℝ) * (1 / (q : ℝ) ^ 2) := by
          apply mul_le_mul h3 hα (abs_nonneg _) (by positivity)
      _ ≤ 1 / (2 * (q : ℝ)) := by
          rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
  -- combine: dist(iα−jα) ≥ dist(d·a/q) − perturbation ≥ 1/q − 1/(2q) = 1/(2q)
  have hcomb := dist_round_le (((d * a : ℤ) : ℝ) / q) ((i : ℝ) * α - (j : ℝ) * α)
  rw [abs_sub_comm (((d * a : ℤ) : ℝ) / q) ((i : ℝ) * α - (j : ℝ) * α)] at hcomb
  have hq2R : 1 / (q : ℝ) - 1 / (2 * (q : ℝ)) = 1 / (2 * (q : ℝ)) := by
    field_simp
    ring
  linarith [hsep, hpert, hcomb, hq2R]

/-- **The min-sum workhorse, uniform-cap form**: for `gcd(a,q) = 1`, `|α − a/q| ≤ 1/q²`,
    `q ≥ 2`, and ANY `R` consecutive integers with a uniform cap `V`,

      `∑_h min(V, 1/(2‖hα‖)) ≤ (R/(q/2) + 1) · (2V + 4q(1 + log 2q))`.

    (Terms with `hα ∈ ℤ` get the `V` cap.) This is the block-summed engine of the
    Type-I/II minor-arc estimates; the classical `N/h`-cap form (Vaughan Lemma 2.2)
    follows by applying this on dyadic `h`-ranges with `V = N/2ᵗ`. -/
lemma range_min_sum_le (a q : ℕ) (hq : 2 ≤ q) (ha : Nat.Coprime a q) (α : ℝ)
    (hα : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (V : ℝ) (hV : 0 ≤ V) (M R : ℕ) :
    ∑ h ∈ Finset.Ico M (M + R),
      (if (h : ℝ) * α - round ((h : ℝ) * α) = 0 then V
       else min V (1 / (2 * |(h : ℝ) * α - round ((h : ℝ) * α)|)))
      ≤ ((R / (q / 2) + 1 : ℕ) : ℝ) * (2 * V + 4 * q * (1 + Real.log (2 * q))) := by
  set L : ℕ := q / 2 with hLdef
  have hL0 : 0 < L := Nat.div_pos hq (by norm_num)
  have h2L : 2 * L ≤ q := by
    have := Nat.div_mul_le_self q 2
    omega
  set T : ℕ := R / L + 1 with hT
  set w : ℕ → ℝ := fun h =>
    (if (h : ℝ) * α - round ((h : ℝ) * α) = 0 then V
     else min V (1 / (2 * |(h : ℝ) * α - round ((h : ℝ) * α)|))) with hw
  have hw0 : ∀ h, 0 ≤ w h := by
    intro h
    rw [hw]
    dsimp only
    split
    · exact hV
    · exact le_min hV (by positivity)
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  -- covering by T blocks of length L
  have hcover : Finset.Ico M (M + R) ⊆
      (Finset.range T).biUnion (fun t => Finset.Ico (M + t * L) (M + t * L + L)) := by
    intro h hh
    simp only [Finset.mem_Ico] at hh
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hh.1
    have hnR : n < R := by omega
    rw [Finset.mem_biUnion]
    refine ⟨n / L, ?_, ?_⟩
    · rw [Finset.mem_range, hT]
      exact Nat.lt_succ_of_le (Nat.div_le_div_right hnR.le)
    · obtain ⟨P, hP⟩ : ∃ P, P = n / L * L := ⟨_, rfl⟩
      obtain ⟨m, hm⟩ : ∃ m, m = n % L := ⟨_, rfl⟩
      have h1 : P ≤ n := hP ▸ Nat.div_mul_le_self n L
      have hdm : P + m = n := by rw [hP, hm]; exact Nat.div_add_mod' n L
      have hmod : m < L := hm ▸ Nat.mod_lt n hL0
      rw [Finset.mem_Ico, ← hP]
      omega
  -- blocks are pairwise disjoint
  have hdisj : (↑(Finset.range T) : Set ℕ).PairwiseDisjoint
      (fun t => Finset.Ico (M + t * L) (M + t * L + L)) := by
    intro t₁ _ t₂ _ hne
    apply Finset.disjoint_left.mpr
    intro h h1 h2
    simp only [Finset.mem_Ico] at h1 h2
    obtain ⟨P₁, hP₁⟩ : ∃ P, P = t₁ * L := ⟨_, rfl⟩
    obtain ⟨P₂, hP₂⟩ : ∃ P, P = t₂ * L := ⟨_, rfl⟩
    rw [← hP₁] at h1
    rw [← hP₂] at h2
    rcases Nat.lt_or_ge t₁ t₂ with hlt | hge
    · have h5 : P₁ + L ≤ P₂ := by
        rw [hP₁, hP₂, ← Nat.succ_mul]
        exact Nat.mul_le_mul_right L (Nat.succ_le_of_lt hlt)
      omega
    · have hlt2 : t₂ < t₁ := lt_of_le_of_ne hge (Ne.symm hne)
      have h5 : P₂ + L ≤ P₁ := by
        rw [hP₁, hP₂, ← Nat.succ_mul]
        exact Nat.mul_le_mul_right L (Nat.succ_le_of_lt hlt2)
      omega
  -- per-block bound via spaced_min_sum_le with δ = 1/(2q)
  have hblock : ∀ t : ℕ, ∑ h ∈ Finset.Ico (M + t * L) (M + t * L + L), w h
      ≤ 2 * V + 4 * (q : ℝ) * (1 + Real.log (2 * q)) := by
    intro t
    have hδpos : (0 : ℝ) < 1 / (2 * (q : ℝ)) := by positivity
    have hδ1 : 1 / (2 * (q : ℝ)) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
      linarith
    have hsp := block_spaced a q (by omega) ha α hα (M + t * L) L h2L
    have happ := spaced_min_sum_le (Finset.Ico (M + t * L) (M + t * L + L))
      (fun h : ℕ => (h : ℝ) * α) (1 / (2 * (q : ℝ))) V hδpos hδ1 hV hsp
    have e1 : (2 : ℝ) / (1 / (2 * (q : ℝ))) = 4 * q := by
      field_simp
      ring
    have e2 : (1 : ℝ) / (1 / (2 * (q : ℝ))) = 2 * q := by
      field_simp
    rw [e1, e2] at happ
    exact happ
  -- assemble
  calc ∑ h ∈ Finset.Ico M (M + R), w h
      ≤ ∑ h ∈ (Finset.range T).biUnion
          (fun t => Finset.Ico (M + t * L) (M + t * L + L)), w h :=
        Finset.sum_le_sum_of_subset_of_nonneg hcover (fun h _ _ => hw0 h)
    _ = ∑ t ∈ Finset.range T, ∑ h ∈ Finset.Ico (M + t * L) (M + t * L + L), w h :=
        Finset.sum_biUnion hdisj
    _ ≤ ∑ _t ∈ Finset.range T, (2 * V + 4 * (q : ℝ) * (1 + Real.log (2 * q))) :=
        Finset.sum_le_sum (fun t _ => hblock t)
    _ = (T : ℝ) * (2 * V + 4 * (q : ℝ) * (1 + Real.log (2 * q))) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ = ((R / (q / 2) + 1 : ℕ) : ℝ) * (2 * V + 4 * q * (1 + Real.log (2 * q))) := by
        rw [hT, hLdef]

/-! ### The exponential-sum chain (self-contained copy of the `MinorArcExpSum.lean` core,
    re-verified here so this file stays standalone for the warm-REPL daemon) -/












/-! ### Type I: the workhorse applied to the inner geometric sums -/


/-- Interval form: `‖∑_{d∈[A,B)} e(dβ)‖` obeys the same capped bound with `M = B−A`
    (shift out the unit-modulus prefactor `e(Aβ)`). Type II's inner `d`-sums need this. -/
lemma exp_sum_Ico_min_bound (β : ℝ) (A B : ℕ) :
    ‖∑ d ∈ Finset.Ico A B, e (d * β)‖
      ≤ (if β - round β = 0 then ((B - A : ℕ) : ℝ)
         else min ((B - A : ℕ) : ℝ) (1 / (2 * |β - round β|))) := by
  have hshift : ∑ d ∈ Finset.Ico A B, e (d * β)
      = e (A * β) * ∑ k ∈ Finset.range (B - A), e (k * β) := by
    rw [Finset.sum_Ico_eq_sum_range, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [e_add]
    congr 1
    push_cast
    ring
  rw [hshift, norm_mul, e_norm, one_mul]
  exact exp_sum_min_bound β (B - A)

/-- **The Type I estimate**: the `d`-sum of inner geometric sums over `[1, D]` is
    controlled by the workhorse — for `gcd(a,q)=1`, `|α − a/q| ≤ 1/q²`, `q ≥ 2`:

      `∑_{d=1}^{D} ‖∑_{n<M} e(ndα)‖ ≤ (D/(q/2) + 1)·(2M + 4q(1 + log 2q))`. -/
lemma typeI_sum_bound (a q : ℕ) (hq : 2 ≤ q) (ha : Nat.Coprime a q) (α : ℝ)
    (hα : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2) (D M : ℕ) :
    ∑ d ∈ Finset.Ico 1 (1 + D), ‖∑ n ∈ Finset.range M, e (n * ((d : ℝ) * α))‖
      ≤ ((D / (q / 2) + 1 : ℕ) : ℝ) * (2 * M + 4 * q * (1 + Real.log (2 * q))) := by
  have hterm : ∀ d ∈ Finset.Ico 1 (1 + D),
      ‖∑ n ∈ Finset.range M, e (n * ((d : ℝ) * α))‖
      ≤ (if (d : ℝ) * α - round ((d : ℝ) * α) = 0 then ((M : ℕ) : ℝ)
         else min ((M : ℕ) : ℝ) (1 / (2 * |(d : ℝ) * α - round ((d : ℝ) * α)|))) :=
    fun d _ => exp_sum_min_bound ((d : ℝ) * α) M
  calc ∑ d ∈ Finset.Ico 1 (1 + D), ‖∑ n ∈ Finset.range M, e (n * ((d : ℝ) * α))‖
      ≤ ∑ d ∈ Finset.Ico 1 (1 + D),
        (if (d : ℝ) * α - round ((d : ℝ) * α) = 0 then ((M : ℕ) : ℝ)
         else min ((M : ℕ) : ℝ) (1 / (2 * |(d : ℝ) * α - round ((d : ℝ) * α)|))) :=
        Finset.sum_le_sum hterm
    _ ≤ ((D / (q / 2) + 1 : ℕ) : ℝ) * (2 * (M : ℝ) + 4 * q * (1 + Real.log (2 * q))) :=
        range_min_sum_le a q hq ha α hα (M : ℝ) (by positivity) 1 D

/-- dist(·,ℤ) is even: `|(-β) − round(-β)| = |β − round β|` (round minimizes both ways). -/
lemma dist_round_neg (β : ℝ) : |(-β) - round (-β)| = |β - round β| := by
  apply le_antisymm
  · calc |(-β) - round (-β)| ≤ |(-β) - ((-(round β) : ℤ) : ℝ)| := round_le (-β) (-(round β))
      _ = |β - round β| := by push_cast; rw [← abs_neg]; ring_nf
  · calc |β - round β| ≤ |β - ((-(round (-β)) : ℤ) : ℝ)| := round_le β (-(round (-β)))
      _ = |(-β) - round (-β)| := by push_cast; rw [← abs_neg]; ring_nf

/-- **Difference-count bound**: each difference `h = m₁ − m₂` occurs for at most `M`
    pairs, so a nonneg function of the difference sums to at most `M` times its
    `h`-sum over `(-M, M)`. -/
lemma diff_count_le (F : ℤ → ℝ) (hF : ∀ h, 0 ≤ F h) (M : ℕ) :
    ∑ m₁ ∈ Finset.range M, ∑ m₂ ∈ Finset.range M, F ((m₁ : ℤ) - m₂)
      ≤ (M : ℝ) * ∑ h ∈ Finset.Icc (-(M : ℤ) + 1) ((M : ℤ) - 1), F h := by
  classical
  have h1 : ∑ m₁ ∈ Finset.range M, ∑ m₂ ∈ Finset.range M, F ((m₁ : ℤ) - m₂)
      = ∑ p ∈ Finset.range M ×ˢ Finset.range M, F ((p.1 : ℤ) - p.2) := by
    rw [Finset.sum_product]
  rw [h1]
  calc ∑ p ∈ Finset.range M ×ˢ Finset.range M, F ((p.1 : ℤ) - p.2)
      = ∑ h ∈ (Finset.range M ×ˢ Finset.range M).image (fun p : ℕ × ℕ => (p.1 : ℤ) - p.2),
          ((Finset.range M ×ˢ Finset.range M).filter
            (fun p : ℕ × ℕ => (p.1 : ℤ) - p.2 = h)).card • F h :=
        Finset.sum_comp _ _
    _ ≤ ∑ h ∈ (Finset.range M ×ˢ Finset.range M).image (fun p : ℕ × ℕ => (p.1 : ℤ) - p.2),
          (M : ℝ) * F h := by
        apply Finset.sum_le_sum
        intro h _
        rw [nsmul_eq_mul]
        apply mul_le_mul_of_nonneg_right _ (hF h)
        have hcard : ((Finset.range M ×ˢ Finset.range M).filter
            (fun p : ℕ × ℕ => (p.1 : ℤ) - p.2 = h)).card ≤ (Finset.range M).card := by
          apply Finset.card_le_card_of_injOn (fun p => p.1)
          · intro p hp
            simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hp
            exact hp.1.1
          · intro p hp p' hp' hpp
            rw [Finset.mem_coe, Finset.mem_filter] at hp hp'
            have hpp' : p.1 = p'.1 := hpp
            have e1 := hp.2
            have e2 := hp'.2
            have h2 : (p.2 : ℤ) = (p'.2 : ℤ) := by omega
            exact Prod.ext hpp' (by exact_mod_cast h2)
        rw [Finset.card_range] at hcard
        exact_mod_cast hcard
    _ ≤ ∑ h ∈ Finset.Icc (-(M : ℤ) + 1) ((M : ℤ) - 1), (M : ℝ) * F h := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro h hh
          simp only [Finset.mem_image, Finset.mem_product, Finset.mem_range] at hh
          obtain ⟨p, ⟨hp1, hp2⟩, rfl⟩ := hh
          rw [Finset.mem_Icc]
          omega
        · intro h _ _
          exact mul_nonneg (by positivity) (hF h)
    _ = (M : ℝ) * ∑ h ∈ Finset.Icc (-(M : ℤ) + 1) ((M : ℤ) - 1), F h :=
        (Finset.mul_sum _ _ _).symm

/-- **Discrete second moment** (Type II opening move): the `d`-averaged square of a
    linear exponential sum is bounded by the bilinear difference sums. -/
lemma typeII_second_moment_le (b : ℕ → ℂ) (M : ℕ) (α : ℝ) (s : Finset ℕ) :
    ∑ d ∈ s, ‖∑ m ∈ Finset.range M, b m * e ((d : ℝ) * (m : ℝ) * α)‖ ^ 2
      ≤ ∑ m₁ ∈ Finset.range M, ∑ m₂ ∈ Finset.range M,
          ‖b m₁‖ * ‖b m₂‖ * ‖∑ d ∈ s, e ((d : ℝ) * (((m₁ : ℝ) - m₂) * α))‖ := by
  -- complex identity: ∑_d S_d·conj(S_d) = ∑_{m₁,m₂} b m₁ conj(b m₂) ∑_d e(d(m₁−m₂)α)
  have hid : ∑ d ∈ s, ((∑ m ∈ Finset.range M, b m * e ((d : ℝ) * (m : ℝ) * α)) *
        (starRingEnd ℂ) (∑ m ∈ Finset.range M, b m * e ((d : ℝ) * (m : ℝ) * α)))
      = ∑ m₁ ∈ Finset.range M, ∑ m₂ ∈ Finset.range M,
          (b m₁ * (starRingEnd ℂ) (b m₂)) *
            ∑ d ∈ s, e ((d : ℝ) * (((m₁ : ℝ) - m₂) * α)) := by
    have hpt : ∀ d ∈ s,
        (∑ m ∈ Finset.range M, b m * e ((d : ℝ) * (m : ℝ) * α)) *
          (starRingEnd ℂ) (∑ m ∈ Finset.range M, b m * e ((d : ℝ) * (m : ℝ) * α))
        = ∑ m₁ ∈ Finset.range M, ∑ m₂ ∈ Finset.range M,
            (b m₁ * (starRingEnd ℂ) (b m₂)) * e ((d : ℝ) * (((m₁ : ℝ) - m₂) * α)) := by
      intro d _
      rw [map_sum, Finset.sum_mul_sum]
      apply Finset.sum_congr rfl; intro m₁ _
      apply Finset.sum_congr rfl; intro m₂ _
      rw [map_mul, e_conj]
      have h1 : e ((d : ℝ) * (m₁ : ℝ) * α) * e (-((d : ℝ) * (m₂ : ℝ) * α))
          = e ((d : ℝ) * (((m₁ : ℝ) - m₂) * α)) := by
        rw [e_add]; congr 1; ring
      calc b m₁ * e ((d : ℝ) * (m₁ : ℝ) * α)
            * ((starRingEnd ℂ) (b m₂) * e (-((d : ℝ) * (m₂ : ℝ) * α)))
          = (b m₁ * (starRingEnd ℂ) (b m₂))
            * (e ((d : ℝ) * (m₁ : ℝ) * α) * e (-((d : ℝ) * (m₂ : ℝ) * α))) := by ring
        _ = (b m₁ * (starRingEnd ℂ) (b m₂)) * e ((d : ℝ) * (((m₁ : ℝ) - m₂) * α)) := by
            rw [h1]
    rw [Finset.sum_congr rfl hpt]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro m₁ _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro m₂ _
    rw [Finset.mul_sum]
  -- take real parts and bound
  have hre : ∑ d ∈ s, ‖∑ m ∈ Finset.range M, b m * e ((d : ℝ) * (m : ℝ) * α)‖ ^ 2
      = (∑ d ∈ s, ((∑ m ∈ Finset.range M, b m * e ((d : ℝ) * (m : ℝ) * α)) *
          (starRingEnd ℂ) (∑ m ∈ Finset.range M, b m * e ((d : ℝ) * (m : ℝ) * α)))).re := by
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro d _
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    exact (Complex.ofReal_re _).symm
  rw [hre, hid]
  calc (∑ m₁ ∈ Finset.range M, ∑ m₂ ∈ Finset.range M,
        (b m₁ * (starRingEnd ℂ) (b m₂)) * ∑ d ∈ s, e ((d : ℝ) * (((m₁ : ℝ) - m₂) * α))).re
      ≤ ‖∑ m₁ ∈ Finset.range M, ∑ m₂ ∈ Finset.range M,
        (b m₁ * (starRingEnd ℂ) (b m₂)) * ∑ d ∈ s, e ((d : ℝ) * (((m₁ : ℝ) - m₂) * α))‖ :=
        Complex.re_le_norm _
    _ ≤ ∑ m₁ ∈ Finset.range M, ‖∑ m₂ ∈ Finset.range M,
        (b m₁ * (starRingEnd ℂ) (b m₂)) * ∑ d ∈ s, e ((d : ℝ) * (((m₁ : ℝ) - m₂) * α))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ m₁ ∈ Finset.range M, ∑ m₂ ∈ Finset.range M,
        ‖(b m₁ * (starRingEnd ℂ) (b m₂)) * ∑ d ∈ s, e ((d : ℝ) * (((m₁ : ℝ) - m₂) * α))‖ :=
        Finset.sum_le_sum (fun m₁ _ => norm_sum_le _ _)
    _ = ∑ m₁ ∈ Finset.range M, ∑ m₂ ∈ Finset.range M,
        ‖b m₁‖ * ‖b m₂‖ * ‖∑ d ∈ s, e ((d : ℝ) * (((m₁ : ℝ) - m₂) * α))‖ := by
        apply Finset.sum_congr rfl; intro m₁ _
        apply Finset.sum_congr rfl; intro m₂ _
        rw [norm_mul, norm_mul, RCLike.norm_conj]

/-- **The Type II h-sum estimate**: the symmetric difference-sum of interval exponential
    sums is one diagonal term plus twice the workhorse. -/
lemma typeII_h_sum_le (a q : ℕ) (hq : 2 ≤ q) (ha : Nat.Coprime a q) (α : ℝ)
    (hα : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2) (A B M : ℕ) :
    ∑ h ∈ Finset.Icc (-(M : ℤ) + 1) ((M : ℤ) - 1),
        ‖∑ d ∈ Finset.Ico A B, e ((d : ℝ) * ((h : ℝ) * α))‖
      ≤ ((B - A : ℕ) : ℝ)
        + 2 * ((((M - 1 : ℕ)) / (q / 2) + 1 : ℕ) : ℝ)
            * (2 * ((B - A : ℕ) : ℝ) + 4 * q * (1 + Real.log (2 * q))) := by
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hlog0 : (0 : ℝ) ≤ Real.log (2 * q) := by
    apply Real.log_nonneg
    have : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    linarith
  set V : ℝ := ((B - A : ℕ) : ℝ) with hV
  have hV0 : 0 ≤ V := by rw [hV]; positivity
  set w : ℤ → ℝ := fun h =>
    (if (h : ℝ) * α - round ((h : ℝ) * α) = 0 then V
     else min V (1 / (2 * |(h : ℝ) * α - round ((h : ℝ) * α)|))) with hw
  have hw0 : ∀ h, 0 ≤ w h := by
    intro h
    rw [hw]
    dsimp only
    split
    · exact hV0
    · exact le_min hV0 (by positivity)
  have hG : ∀ h : ℤ, ‖∑ d ∈ Finset.Ico A B, e ((d : ℝ) * ((h : ℝ) * α))‖ ≤ w h := by
    intro h
    rw [hw]
    exact exp_sum_Ico_min_bound ((h : ℝ) * α) A B
  have hweven : ∀ h : ℤ, w (-h) = w h := by
    intro h
    rw [hw]
    dsimp only
    have hcast : ((-h : ℤ) : ℝ) * α = -((h : ℝ) * α) := by push_cast; ring
    rw [hcast]
    have hd := dist_round_neg ((h : ℝ) * α)
    by_cases h0 : (h : ℝ) * α - round ((h : ℝ) * α) = 0
    · have h0' : -((h : ℝ) * α) - round (-((h : ℝ) * α)) = 0 := by
        have := hd
        rw [abs_eq_zero.mpr h0] at this
        exact abs_eq_zero.mp this
      rw [if_pos h0, if_pos h0']
    · have h0' : ¬ (-((h : ℝ) * α) - round (-((h : ℝ) * α)) = 0) := by
        intro hc
        apply h0
        have := hd
        rw [abs_eq_zero.mpr hc] at this
        exact abs_eq_zero.mp this.symm
      rw [if_neg h0, if_neg h0', hd]
  have hstep1 : ∑ h ∈ Finset.Icc (-(M : ℤ) + 1) ((M : ℤ) - 1),
        ‖∑ d ∈ Finset.Ico A B, e ((d : ℝ) * ((h : ℝ) * α))‖
      ≤ ∑ h ∈ Finset.Icc (-(M : ℤ) + 1) ((M : ℤ) - 1), w h :=
    Finset.sum_le_sum (fun h _ => hG h)
  rcases Nat.eq_zero_or_pos M with hM0 | hM1
  · subst hM0
    simp only [Nat.cast_zero, neg_zero, zero_add, zero_sub] at hstep1 ⊢
    rw [show Finset.Icc (1 : ℤ) (-1) = ∅ from Finset.Icc_eq_empty (by omega)] at hstep1 ⊢
    simp only [Finset.sum_empty] at hstep1 ⊢
    positivity
  have hK : (0 : ℤ) ≤ (M : ℤ) - 1 := by omega
  have hsplit : Finset.Icc (-(M : ℤ) + 1) ((M : ℤ) - 1)
      = (Finset.Icc (-(M : ℤ) + 1) (-1)) ∪ insert 0 (Finset.Icc 1 ((M : ℤ) - 1)) := by
    ext h
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_insert]
    omega
  have hdisj : Disjoint (Finset.Icc (-(M : ℤ) + 1) (-1))
      (insert 0 (Finset.Icc 1 ((M : ℤ) - 1))) := by
    rw [Finset.disjoint_left]
    intro h h1 h2
    simp only [Finset.mem_Icc] at h1
    simp only [Finset.mem_insert, Finset.mem_Icc] at h2
    omega
  have h0notin : (0 : ℤ) ∉ Finset.Icc 1 ((M : ℤ) - 1) := by
    simp only [Finset.mem_Icc]
    omega
  have hrefl : ∑ h ∈ Finset.Icc (-(M : ℤ) + 1) (-1), w h
      = ∑ h ∈ Finset.Icc 1 ((M : ℤ) - 1), w h := by
    apply Finset.sum_nbij' (i := fun h => -h) (j := fun h => -h)
    · intro h hh; simp only [Finset.mem_Icc] at *; omega
    · intro h hh; simp only [Finset.mem_Icc] at *; omega
    · intro h _; ring
    · intro h _; ring
    · intro h _
      rw [← hweven h]
  have hw0val : w 0 = V := by
    rw [hw]
    dsimp only
    rw [if_pos (by simp)]
  have hpos : ∑ h ∈ Finset.Icc 1 ((M : ℤ) - 1), w h
      ≤ ((((M - 1 : ℕ)) / (q / 2) + 1 : ℕ) : ℝ)
          * (2 * V + 4 * q * (1 + Real.log (2 * q))) := by
    have hreidx : ∑ h ∈ Finset.Icc 1 ((M : ℤ) - 1), w h
        = ∑ n ∈ Finset.Ico 1 (1 + (M - 1)),
            (if (n : ℝ) * α - round ((n : ℝ) * α) = 0 then V
             else min V (1 / (2 * |(n : ℝ) * α - round ((n : ℝ) * α)|))) := by
      apply Finset.sum_nbij' (i := fun h : ℤ => h.toNat) (j := fun n : ℕ => (n : ℤ))
      · intro h hh; simp only [Finset.mem_Icc] at hh; simp only [Finset.mem_Ico]; omega
      · intro n hn; simp only [Finset.mem_Ico] at hn; simp only [Finset.mem_Icc]; omega
      · intro h hh; simp only [Finset.mem_Icc] at hh; omega
      · intro n hn; simp only [Finset.mem_Ico] at hn; omega
      · intro h hh
        simp only [Finset.mem_Icc] at hh
        rw [hw]
        dsimp only
        have hcast : ((h.toNat : ℕ) : ℝ) = (h : ℝ) := by
          have := Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ h)
          exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) this
        rw [hcast]
    rw [hreidx]
    exact range_min_sum_le a q hq ha α hα V hV0 1 (M - 1)
  calc ∑ h ∈ Finset.Icc (-(M : ℤ) + 1) ((M : ℤ) - 1),
        ‖∑ d ∈ Finset.Ico A B, e ((d : ℝ) * ((h : ℝ) * α))‖
      ≤ ∑ h ∈ Finset.Icc (-(M : ℤ) + 1) ((M : ℤ) - 1), w h := hstep1
    _ = ∑ h ∈ Finset.Icc (-(M : ℤ) + 1) (-1), w h
        + (w 0 + ∑ h ∈ Finset.Icc 1 ((M : ℤ) - 1), w h) := by
        rw [hsplit, Finset.sum_union hdisj, Finset.sum_insert h0notin]
    _ = V + 2 * ∑ h ∈ Finset.Icc 1 ((M : ℤ) - 1), w h := by
        rw [hrefl, hw0val]; ring
    _ ≤ V + 2 * (((((M - 1 : ℕ)) / (q / 2) + 1 : ℕ) : ℝ)
          * (2 * V + 4 * q * (1 + Real.log (2 * q)))) := by
        have := hpos
        linarith
    _ = ((B - A : ℕ) : ℝ)
        + 2 * ((((M - 1 : ℕ)) / (q / 2) + 1 : ℕ) : ℝ)
            * (2 * ((B - A : ℕ) : ℝ) + 4 * q * (1 + Real.log (2 * q))) := by
        rw [hV]; ring

/-- **Abel-summation exponential-sum bound**: a monotone nonneg weight `w ≤ W` costs only
    a factor `2W` over the unweighted capped bound. (Feeds the log-weighted Type I sums
    in the Vaughan combine.) -/
lemma abel_exp_sum (w : ℕ → ℝ) (hw0 : ∀ m, 0 ≤ w m) (hwmono : Monotone w)
    (W : ℝ) (hW : ∀ m, w m ≤ W) (β : ℝ) (M : ℕ) :
    ‖∑ m ∈ Finset.range M, (w m : ℂ) * e (m * β)‖
      ≤ 2 * W * (if β - round β = 0 then (M : ℝ)
                 else min (M : ℝ) (1 / (2 * |β - round β|))) := by
  have hW0 : 0 ≤ W := le_trans (hw0 0) (hW 0)
  set cap : ℝ := (if β - round β = 0 then (M : ℝ)
                  else min (M : ℝ) (1 / (2 * |β - round β|))) with hcap
  have hcap0 : 0 ≤ cap := by
    rw [hcap]
    split
    · positivity
    · exact le_min (by positivity) (by positivity)
  have hZ : ∀ k, k ≤ M → ‖∑ j ∈ Finset.range k, e (j * β)‖ ≤ cap := by
    intro k hk
    have h1 := exp_sum_min_bound β k
    rw [hcap]
    have hkM : ((k : ℕ) : ℝ) ≤ (M : ℝ) := by exact_mod_cast hk
    split
    · rename_i h0
      rw [if_pos h0] at h1
      linarith
    · rename_i h0
      rw [if_neg h0] at h1
      exact le_trans h1 (min_le_min hkM le_rfl)
  rcases Nat.eq_zero_or_pos M with hM0 | hM1
  · subst hM0
    simp only [Finset.range_zero, Finset.sum_empty, norm_zero]
    positivity
  have habel : ∑ m ∈ Finset.range M, (w m : ℂ) * e (m * β)
      = (w (M - 1) : ℂ) * ∑ j ∈ Finset.range M, e (j * β)
        - ∑ i ∈ Finset.range (M - 1),
            ((w (i + 1) : ℂ) - w i) * ∑ j ∈ Finset.range (i + 1), e (j * β) := by
    have := Finset.sum_range_by_parts (f := fun m => ((w m : ℝ) : ℂ))
      (g := fun m => e (m * β)) (n := M)
    simpa only [smul_eq_mul] using this
  rw [habel]
  calc ‖(w (M - 1) : ℂ) * ∑ j ∈ Finset.range M, e (j * β)
        - ∑ i ∈ Finset.range (M - 1),
            ((w (i + 1) : ℂ) - w i) * ∑ j ∈ Finset.range (i + 1), e (j * β)‖
      ≤ ‖(w (M - 1) : ℂ) * ∑ j ∈ Finset.range M, e (j * β)‖
        + ‖∑ i ∈ Finset.range (M - 1),
            ((w (i + 1) : ℂ) - w i) * ∑ j ∈ Finset.range (i + 1), e (j * β)‖ :=
        norm_sub_le _ _
    _ ≤ W * cap + ∑ i ∈ Finset.range (M - 1),
          (w (i + 1) - w i) * cap := by
        apply add_le_add
        · rw [norm_mul, Complex.norm_real]
          have h1 : |w (M - 1)| ≤ W := by rw [abs_of_nonneg (hw0 _)]; exact hW _
          exact mul_le_mul h1 (hZ M le_rfl) (norm_nonneg _) hW0
        · calc ‖∑ i ∈ Finset.range (M - 1),
                ((w (i + 1) : ℂ) - w i) * ∑ j ∈ Finset.range (i + 1), e (j * β)‖
              ≤ ∑ i ∈ Finset.range (M - 1),
                ‖((w (i + 1) : ℂ) - w i) * ∑ j ∈ Finset.range (i + 1), e (j * β)‖ :=
                norm_sum_le _ _
            _ ≤ ∑ i ∈ Finset.range (M - 1), (w (i + 1) - w i) * cap := by
                apply Finset.sum_le_sum
                intro i hi
                simp only [Finset.mem_range] at hi
                rw [norm_mul]
                have hcast : ((w (i + 1) : ℂ) - w i) = ((w (i + 1) - w i : ℝ) : ℂ) := by
                  push_cast; ring
                rw [hcast, Complex.norm_real, Real.norm_eq_abs,
                  abs_of_nonneg (by linarith [hwmono (Nat.le_succ i)] : (0:ℝ) ≤ w (i+1) - w i)]
                apply mul_le_mul_of_nonneg_left _ (by linarith [hwmono (Nat.le_succ i)])
                exact hZ (i + 1) (by omega)
    _ = W * cap + (w (M - 1) - w 0) * cap := by
        congr 1
        rw [← Finset.sum_mul]
        congr 1
        exact Finset.sum_range_sub (fun i => w i) (M - 1)
    _ ≤ W * cap + W * cap := by
        have h4 : w (M - 1) - w 0 ≤ W := by linarith [hW (M - 1), hw0 0]
        have h5 := mul_le_mul_of_nonneg_right h4 hcap0
        linarith
    _ = 2 * W * cap := by ring

/-- (A) The Type II second moment through the workhorse chain. -/
lemma typeII_second_moment_workhorse (a q : ℕ) (hq : 2 ≤ q) (ha : Nat.Coprime a q) (α : ℝ)
    (hα : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (b : ℕ → ℂ) (Binf : ℝ) (hb : ∀ m, ‖b m‖ ≤ Binf)
    (A B M : ℕ) :
    ∑ d ∈ Finset.Ico A B, ‖∑ m ∈ Finset.range M, b m * e ((d : ℝ) * (m : ℝ) * α)‖ ^ 2
      ≤ Binf ^ 2 * (M : ℝ) *
          (((B - A : ℕ) : ℝ)
            + 2 * ((((M - 1 : ℕ)) / (q / 2) + 1 : ℕ) : ℝ)
                * (2 * ((B - A : ℕ) : ℝ) + 4 * q * (1 + Real.log (2 * q)))) := by
  have hB0 : 0 ≤ Binf := le_trans (norm_nonneg _) (hb 0)
  have h3a := typeII_second_moment_le b M α (Finset.Ico A B)
  have h3b : ∑ m₁ ∈ Finset.range M, ∑ m₂ ∈ Finset.range M,
      ‖b m₁‖ * ‖b m₂‖ * ‖∑ d ∈ Finset.Ico A B, e ((d : ℝ) * (((m₁ : ℝ) - m₂) * α))‖
      ≤ Binf ^ 2 * ∑ m₁ ∈ Finset.range M, ∑ m₂ ∈ Finset.range M,
          ‖∑ d ∈ Finset.Ico A B, e ((d : ℝ) * (((((m₁ : ℤ) - m₂) : ℤ) : ℝ) * α))‖ := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro m₁ _
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro m₂ _
    have hsum_eq : ∑ d ∈ Finset.Ico A B, e ((d : ℝ) * (((m₁ : ℝ) - m₂) * α))
        = ∑ d ∈ Finset.Ico A B, e ((d : ℝ) * (((((m₁ : ℤ) - m₂) : ℤ) : ℝ) * α)) :=
      Finset.sum_congr rfl (fun d _ => congrArg e (by push_cast; ring))
    rw [hsum_eq, pow_two]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact mul_le_mul (hb m₁) (hb m₂) (norm_nonneg _) hB0
  have h3c := diff_count_le
    (fun h => ‖∑ d ∈ Finset.Ico A B, e ((d : ℝ) * ((h : ℝ) * α))‖)
    (fun h => norm_nonneg _) M
  have h3d := typeII_h_sum_le a q hq ha α hα A B M
  have hM0 : (0 : ℝ) ≤ (M : ℝ) := by positivity
  have hB2 : (0 : ℝ) ≤ Binf ^ 2 := by positivity
  calc ∑ d ∈ Finset.Ico A B, ‖∑ m ∈ Finset.range M, b m * e ((d : ℝ) * (m : ℝ) * α)‖ ^ 2
      ≤ ∑ m₁ ∈ Finset.range M, ∑ m₂ ∈ Finset.range M,
          ‖b m₁‖ * ‖b m₂‖ * ‖∑ d ∈ Finset.Ico A B, e ((d : ℝ) * (((m₁ : ℝ) - m₂) * α))‖ :=
        h3a
    _ ≤ Binf ^ 2 * ∑ m₁ ∈ Finset.range M, ∑ m₂ ∈ Finset.range M,
          ‖∑ d ∈ Finset.Ico A B, e ((d : ℝ) * (((((m₁ : ℤ) - m₂) : ℤ) : ℝ) * α))‖ := h3b
    _ ≤ Binf ^ 2 * ((M : ℝ) * ∑ h ∈ Finset.Icc (-(M : ℤ) + 1) ((M : ℤ) - 1),
          ‖∑ d ∈ Finset.Ico A B, e ((d : ℝ) * ((h : ℝ) * α))‖) :=
        mul_le_mul_of_nonneg_left h3c hB2
    _ ≤ Binf ^ 2 * ((M : ℝ) * (((B - A : ℕ) : ℝ)
          + 2 * ((((M - 1 : ℕ)) / (q / 2) + 1 : ℕ) : ℝ)
              * (2 * ((B - A : ℕ) : ℝ) + 4 * q * (1 + Real.log (2 * q))))) := by
        apply mul_le_mul_of_nonneg_left _ hB2
        exact mul_le_mul_of_nonneg_left h3d hM0
    _ = Binf ^ 2 * (M : ℝ) *
        (((B - A : ℕ) : ℝ)
          + 2 * ((((M - 1 : ℕ)) / (q / 2) + 1 : ℕ) : ℝ)
              * (2 * ((B - A : ℕ) : ℝ) + 4 * q * (1 + Real.log (2 * q)))) := by ring

/-- **THE TYPE II (BILINEAR) ESTIMATE**: squared, with sup-bounded coefficients — for
    `gcd(a,q)=1`, `|α − a/q| ≤ 1/q²`, `q ≥ 2`:

      `‖∑_{d∈[A,B)} c_d ∑_{m<M} b_m e(dmα)‖² ≤ A∞²(B−A) · B∞²M · [workhorse bound]`. -/
lemma typeII_bilinear_sq_le (a q : ℕ) (hq : 2 ≤ q) (ha : Nat.Coprime a q) (α : ℝ)
    (hα : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (c b : ℕ → ℂ) (Ainf Binf : ℝ)
    (hc : ∀ d, ‖c d‖ ≤ Ainf) (hb : ∀ m, ‖b m‖ ≤ Binf)
    (A B M : ℕ) :
    ‖∑ d ∈ Finset.Ico A B, c d * ∑ m ∈ Finset.range M, b m * e ((d : ℝ) * (m : ℝ) * α)‖ ^ 2
      ≤ Ainf ^ 2 * ((B - A : ℕ) : ℝ) * (Binf ^ 2 * (M : ℝ) *
          (((B - A : ℕ) : ℝ)
            + 2 * ((((M - 1 : ℕ)) / (q / 2) + 1 : ℕ) : ℝ)
                * (2 * ((B - A : ℕ) : ℝ) + 4 * q * (1 + Real.log (2 * q))))) := by
  have hA0 : 0 ≤ Ainf := le_trans (norm_nonneg _) (hc 0)
  have h1 : ‖∑ d ∈ Finset.Ico A B, c d * ∑ m ∈ Finset.range M, b m * e ((d : ℝ) * (m : ℝ) * α)‖
      ≤ Ainf * ∑ d ∈ Finset.Ico A B,
          ‖∑ m ∈ Finset.range M, b m * e ((d : ℝ) * (m : ℝ) * α)‖ := by
    calc ‖∑ d ∈ Finset.Ico A B, c d * ∑ m ∈ Finset.range M, b m * e ((d : ℝ) * (m : ℝ) * α)‖
        ≤ ∑ d ∈ Finset.Ico A B, ‖c d * ∑ m ∈ Finset.range M, b m * e ((d : ℝ) * (m : ℝ) * α)‖ :=
          norm_sum_le _ _
      _ = ∑ d ∈ Finset.Ico A B,
            ‖c d‖ * ‖∑ m ∈ Finset.range M, b m * e ((d : ℝ) * (m : ℝ) * α)‖ := by
          apply Finset.sum_congr rfl; intro d _; rw [norm_mul]
      _ ≤ ∑ d ∈ Finset.Ico A B,
            Ainf * ‖∑ m ∈ Finset.range M, b m * e ((d : ℝ) * (m : ℝ) * α)‖ :=
          Finset.sum_le_sum (fun d _ => mul_le_mul_of_nonneg_right (hc d) (norm_nonneg _))
      _ = Ainf * ∑ d ∈ Finset.Ico A B,
            ‖∑ m ∈ Finset.range M, b m * e ((d : ℝ) * (m : ℝ) * α)‖ :=
          (Finset.mul_sum _ _ _).symm
  have h2 : (∑ d ∈ Finset.Ico A B, ‖∑ m ∈ Finset.range M, b m * e ((d : ℝ) * (m : ℝ) * α)‖) ^ 2
      ≤ ((B - A : ℕ) : ℝ) * ∑ d ∈ Finset.Ico A B,
          ‖∑ m ∈ Finset.range M, b m * e ((d : ℝ) * (m : ℝ) * α)‖ ^ 2 := by
    have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.Ico A B)
      (f := fun d => ‖∑ m ∈ Finset.range M, b m * e ((d : ℝ) * (m : ℝ) * α)‖)
    rw [Nat.card_Ico] at hcs
    exact_mod_cast hcs
  have h3 := typeII_second_moment_workhorse a q hq ha α hα b Binf hb A B M
  calc ‖∑ d ∈ Finset.Ico A B, c d * ∑ m ∈ Finset.range M, b m * e ((d : ℝ) * (m : ℝ) * α)‖ ^ 2
      ≤ (Ainf * ∑ d ∈ Finset.Ico A B,
          ‖∑ m ∈ Finset.range M, b m * e ((d : ℝ) * (m : ℝ) * α)‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ = Ainf ^ 2 * (∑ d ∈ Finset.Ico A B,
          ‖∑ m ∈ Finset.range M, b m * e ((d : ℝ) * (m : ℝ) * α)‖) ^ 2 := by ring
    _ ≤ Ainf ^ 2 * (((B - A : ℕ) : ℝ) * ∑ d ∈ Finset.Ico A B,
          ‖∑ m ∈ Finset.range M, b m * e ((d : ℝ) * (m : ℝ) * α)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ ≤ Ainf ^ 2 * (((B - A : ℕ) : ℝ) * (Binf ^ 2 * (M : ℝ) *
          (((B - A : ℕ) : ℝ)
            + 2 * ((((M - 1 : ℕ)) / (q / 2) + 1 : ℕ) : ℝ)
                * (2 * ((B - A : ℕ) : ℝ) + 4 * q * (1 + Real.log (2 * q)))))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = Ainf ^ 2 * ((B - A : ℕ) : ℝ) * (Binf ^ 2 * (M : ℝ) *
          (((B - A : ℕ) : ℝ)
            + 2 * ((((M - 1 : ℕ)) / (q / 2) + 1 : ℕ) : ℝ)
                * (2 * ((B - A : ℕ) : ℝ) + 4 * q * (1 + Real.log (2 * q))))) := by ring

open ArithmeticFunction in
/-- **Weighted hyperbola unfolding** (the convolution → double-sum bridge of the
    Vaughan combine): for any weight `w : ℕ → ℂ`,
    `∑_{n≤N} (f∗g)(n)·w(n) = ∑_{d·m≤N} f(d)g(m)·w(dm)`. Applying this with
    `w n = e(nα)` to the four terms of `Vaughan.vaughan_identity` yields the
    S₁–S₄ decomposition that Type I / Abel / Type II bound. -/
lemma sum_Ioc_mul_weight (f g : ArithmeticFunction ℝ) (w : ℕ → ℂ) (N : ℕ) :
    ∑ n ∈ Finset.Ioc 0 N, ((f * g) n : ℂ) * w n
      = ∑ x ∈ (Finset.Ioc 0 N ×ˢ Finset.Ioc 0 N).filter (fun x => x.1 * x.2 ≤ N),
          (f x.1 : ℂ) * (g x.2 : ℂ) * w (x.1 * x.2) := by
  have step1 : ∑ n ∈ Finset.Ioc 0 N, ((f * g) n : ℂ) * w n
      = ∑ n ∈ Finset.Ioc 0 N,
          ∑ x ∈ (Finset.Ioc 0 N ×ˢ Finset.Ioc 0 N).filter (fun x => x.1 * x.2 = n),
            (f x.1 : ℂ) * (g x.2 : ℂ) * w (x.1 * x.2) := by
    apply Finset.sum_congr rfl
    intro n hn
    simp only [Finset.mem_Ioc] at hn
    have hexp : ((f * g) n : ℂ) * w n
        = ∑ x ∈ n.divisorsAntidiagonal, (f x.1 : ℂ) * (g x.2 : ℂ) * w n := by
      rw [ArithmeticFunction.mul_apply]
      push_cast
      rw [Finset.sum_mul]
    rw [hexp, Nat.divisorsAntidiagonal_eq_prod_filter_of_le hn.1.ne' hn.2]
    apply Finset.sum_congr rfl
    intro x hx
    simp only [Finset.mem_filter] at hx
    rw [hx.2]
  rw [step1]
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  simp only [Finset.mem_product, Finset.mem_Ioc] at hx
  have hpos : 0 < x.1 * x.2 := Nat.mul_pos hx.1.1 hx.2.1
  rw [Finset.sum_ite_eq (Finset.Ioc 0 N) (x.1 * x.2)
    (fun _ => (f x.1 : ℂ) * (g x.2 : ℂ) * w (x.1 * x.2))]
  simp only [Finset.mem_Ioc]
  congr 1
  simp only [eq_iff_iff]
  constructor
  · intro h; exact h.2
  · intro h; exact ⟨hpos, h⟩

/-- **The symmetric cap-sum**: `∑_{|h|<M} cap(hα, W) ≤ W + 2((M−1)/(q/2)+1)(2W + 4q(1+log 2q))`
    for any nonneg cap size `W` — the pure-cap form of the Type II h-sum. -/
lemma cap_symmetric_sum_le (a q : ℕ) (hq : 2 ≤ q) (ha : Nat.Coprime a q) (α : ℝ)
    (hα : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2) (W : ℝ) (hW : 0 ≤ W) (M : ℕ) :
    ∑ h ∈ Finset.Icc (-(M : ℤ) + 1) ((M : ℤ) - 1),
      (if (h : ℝ) * α - round ((h : ℝ) * α) = 0 then W
       else min W (1 / (2 * |(h : ℝ) * α - round ((h : ℝ) * α)|)))
      ≤ W + 2 * ((((M - 1 : ℕ)) / (q / 2) + 1 : ℕ) : ℝ)
          * (2 * W + 4 * q * (1 + Real.log (2 * q))) := by
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hlog0 : (0 : ℝ) ≤ Real.log (2 * q) := by
    apply Real.log_nonneg
    have : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    linarith
  set w : ℤ → ℝ := fun h =>
    (if (h : ℝ) * α - round ((h : ℝ) * α) = 0 then W
     else min W (1 / (2 * |(h : ℝ) * α - round ((h : ℝ) * α)|))) with hw
  have hw0 : ∀ h, 0 ≤ w h := by
    intro h
    rw [hw]
    dsimp only
    split
    · exact hW
    · exact le_min hW (by positivity)
  have hweven : ∀ h : ℤ, w (-h) = w h := by
    intro h
    rw [hw]
    dsimp only
    have hcast : ((-h : ℤ) : ℝ) * α = -((h : ℝ) * α) := by push_cast; ring
    rw [hcast]
    have hd := dist_round_neg ((h : ℝ) * α)
    by_cases h0 : (h : ℝ) * α - round ((h : ℝ) * α) = 0
    · have h0' : -((h : ℝ) * α) - round (-((h : ℝ) * α)) = 0 := by
        have := hd
        rw [abs_eq_zero.mpr h0] at this
        exact abs_eq_zero.mp this
      rw [if_pos h0, if_pos h0']
    · have h0' : ¬ (-((h : ℝ) * α) - round (-((h : ℝ) * α)) = 0) := by
        intro hc
        apply h0
        have := hd
        rw [abs_eq_zero.mpr hc] at this
        exact abs_eq_zero.mp this.symm
      rw [if_neg h0, if_neg h0', hd]
  rcases Nat.eq_zero_or_pos M with hM0 | hM1
  · subst hM0
    simp only [Nat.cast_zero, neg_zero, zero_add, zero_sub]
    rw [show Finset.Icc (1 : ℤ) (-1) = ∅ from Finset.Icc_eq_empty (by omega)]
    simp only [Finset.sum_empty]
    have h1 : (0 : ℝ) ≤ 2 * W + 4 * q * (1 + Real.log (2 * q)) := by
      have : (0 : ℝ) ≤ 4 * q * (1 + Real.log (2 * q)) :=
        mul_nonneg (by positivity) (by linarith)
      linarith
    have h2 : (0 : ℝ) ≤ 2 * ((((0 - 1 : ℕ)) / (q / 2) + 1 : ℕ) : ℝ)
        * (2 * W + 4 * q * (1 + Real.log (2 * q))) := by
      apply mul_nonneg (by positivity) h1
    linarith
  have hsplit : Finset.Icc (-(M : ℤ) + 1) ((M : ℤ) - 1)
      = (Finset.Icc (-(M : ℤ) + 1) (-1)) ∪ insert 0 (Finset.Icc 1 ((M : ℤ) - 1)) := by
    ext h
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_insert]
    omega
  have hdisj : Disjoint (Finset.Icc (-(M : ℤ) + 1) (-1))
      (insert 0 (Finset.Icc 1 ((M : ℤ) - 1))) := by
    rw [Finset.disjoint_left]
    intro h h1 h2
    simp only [Finset.mem_Icc] at h1
    simp only [Finset.mem_insert, Finset.mem_Icc] at h2
    omega
  have h0notin : (0 : ℤ) ∉ Finset.Icc 1 ((M : ℤ) - 1) := by
    simp only [Finset.mem_Icc]
    omega
  have hrefl : ∑ h ∈ Finset.Icc (-(M : ℤ) + 1) (-1), w h
      = ∑ h ∈ Finset.Icc 1 ((M : ℤ) - 1), w h := by
    apply Finset.sum_nbij' (i := fun h => -h) (j := fun h => -h)
    · intro h hh; simp only [Finset.mem_Icc] at *; omega
    · intro h hh; simp only [Finset.mem_Icc] at *; omega
    · intro h _; ring
    · intro h _; ring
    · intro h _
      rw [← hweven h]
  have hw0val : w 0 = W := by
    rw [hw]
    dsimp only
    rw [if_pos (by simp)]
  have hpos : ∑ h ∈ Finset.Icc 1 ((M : ℤ) - 1), w h
      ≤ ((((M - 1 : ℕ)) / (q / 2) + 1 : ℕ) : ℝ)
          * (2 * W + 4 * q * (1 + Real.log (2 * q))) := by
    have hreidx : ∑ h ∈ Finset.Icc 1 ((M : ℤ) - 1), w h
        = ∑ n ∈ Finset.Ico 1 (1 + (M - 1)),
            (if (n : ℝ) * α - round ((n : ℝ) * α) = 0 then W
             else min W (1 / (2 * |(n : ℝ) * α - round ((n : ℝ) * α)|))) := by
      apply Finset.sum_nbij' (i := fun h : ℤ => h.toNat) (j := fun n : ℕ => (n : ℤ))
      · intro h hh; simp only [Finset.mem_Icc] at hh; simp only [Finset.mem_Ico]; omega
      · intro n hn; simp only [Finset.mem_Ico] at hn; simp only [Finset.mem_Icc]; omega
      · intro h hh; simp only [Finset.mem_Icc] at hh; omega
      · intro n hn; simp only [Finset.mem_Ico] at hn; omega
      · intro h hh
        simp only [Finset.mem_Icc] at hh
        rw [hw]
        dsimp only
        have hcast : ((h.toNat : ℕ) : ℝ) = (h : ℝ) := by
          have := Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ h)
          exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) this
        rw [hcast]
    rw [hreidx]
    exact range_min_sum_le a q hq ha α hα W hW 1 (M - 1)
  calc ∑ h ∈ Finset.Icc (-(M : ℤ) + 1) ((M : ℤ) - 1), w h
      = ∑ h ∈ Finset.Icc (-(M : ℤ) + 1) (-1), w h
        + (w 0 + ∑ h ∈ Finset.Icc 1 ((M : ℤ) - 1), w h) := by
        rw [hsplit, Finset.sum_union hdisj, Finset.sum_insert h0notin]
    _ = W + 2 * ∑ h ∈ Finset.Icc 1 ((M : ℤ) - 1), w h := by
        rw [hrefl, hw0val]; ring
    _ ≤ W + 2 * (((((M - 1 : ℕ)) / (q / 2) + 1 : ℕ) : ℝ)
          * (2 * W + 4 * q * (1 + Real.log (2 * q)))) := by
        linarith [hpos]
    _ = W + 2 * ((((M - 1 : ℕ)) / (q / 2) + 1 : ℕ) : ℝ)
          * (2 * W + 4 * q * (1 + Real.log (2 * q))) := by ring

/-- **The hyperbola-restricted interval cap**: the doubly-constrained d-sum is still an
    interval, and its cap is uniform in `B − A`. -/
lemma filtered_exp_sum_cap (β : ℝ) (N A B m₁ m₂ : ℕ) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) :
    ‖∑ d ∈ (Finset.Ico A B).filter (fun d => d * m₁ ≤ N ∧ d * m₂ ≤ N), e (d * β)‖
      ≤ (if β - round β = 0 then ((B - A : ℕ) : ℝ)
         else min ((B - A : ℕ) : ℝ) (1 / (2 * |β - round β|))) := by
  have hset : (Finset.Ico A B).filter (fun d => d * m₁ ≤ N ∧ d * m₂ ≤ N)
      = Finset.Ico A (min B (min (N / m₁) (N / m₂) + 1)) := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Ico, lt_min_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      refine ⟨h1, h2, ?_⟩
      have e1 : d ≤ N / m₁ := Nat.le_div_iff_mul_le hm₁ |>.mpr h3
      have e2 : d ≤ N / m₂ := Nat.le_div_iff_mul_le hm₂ |>.mpr h4
      omega
    · rintro ⟨h1, h2, h3⟩
      have e1 : d ≤ N / m₁ := by omega
      have e2 : d ≤ N / m₂ := by omega
      exact ⟨⟨h1, h2⟩, (Nat.le_div_iff_mul_le hm₁).mp e1, (Nat.le_div_iff_mul_le hm₂).mp e2⟩
  rw [hset]
  have h1 := exp_sum_Ico_min_bound β A (min B (min (N / m₁) (N / m₂) + 1))
  have hsize : ((min B (min (N / m₁) (N / m₂) + 1) - A : ℕ) : ℝ) ≤ ((B - A : ℕ) : ℝ) := by
    have : (min B (min (N / m₁) (N / m₂) + 1) - A : ℕ) ≤ (B - A : ℕ) := by omega
    exact_mod_cast this
  split at h1 <;> rename_i hcase
  · rw [if_pos hcase]
    linarith
  · rw [if_neg hcase]
    exact le_trans h1 (min_le_min hsize le_rfl)

/-- **The hyperbola second-moment expansion** (S₄'s centerpiece): the varying `m`-ranges
    `(V, N/d]` are absorbed into interval-restricted `d`-sums. -/
lemma hyperbola_second_moment_expand (g : ℕ → ℝ) (α : ℝ) (N A B V : ℕ) (hA : 0 < A) :
    ∑ d ∈ Finset.Ico A B,
      ‖∑ m ∈ Finset.Ioc V (N / d), (g m : ℂ) * e ((d : ℝ) * (m : ℝ) * α)‖ ^ 2
      ≤ ∑ m₁ ∈ Finset.Ioc V (N / A), ∑ m₂ ∈ Finset.Ioc V (N / A),
          |g m₁| * |g m₂| *
            ‖∑ d ∈ (Finset.Ico A B).filter (fun d => d * m₁ ≤ N ∧ d * m₂ ≤ N),
              e ((d : ℝ) * (((m₁ : ℝ) - m₂) * α))‖ := by
  -- extend each inner sum to the fixed range with indicator coefficients
  have hext : ∀ d ∈ Finset.Ico A B,
      ∑ m ∈ Finset.Ioc V (N / d), (g m : ℂ) * e ((d : ℝ) * (m : ℝ) * α)
      = ∑ m ∈ Finset.Ioc V (N / A),
          ((if d * m ≤ N then g m else 0 : ℝ) : ℂ) * e ((d : ℝ) * (m : ℝ) * α) := by
    intro d hd
    simp only [Finset.mem_Ico] at hd
    have hd0 : 0 < d := lt_of_lt_of_le hA hd.1
    have hstep : ∑ m ∈ Finset.Ioc V (N / d), (g m : ℂ) * e ((d : ℝ) * (m : ℝ) * α)
        = ∑ m ∈ Finset.Ioc V (N / d),
            ((if d * m ≤ N then g m else 0 : ℝ) : ℂ) * e ((d : ℝ) * (m : ℝ) * α) := by
      apply Finset.sum_congr rfl
      intro m hm
      simp only [Finset.mem_Ioc] at hm
      rw [if_pos (by rw [mul_comm]; exact (Nat.le_div_iff_mul_le hd0).mp hm.2)]
    rw [hstep]
    apply Finset.sum_subset
    · intro m hm
      simp only [Finset.mem_Ioc] at hm ⊢
      exact ⟨hm.1, le_trans hm.2 (Nat.div_le_div_left hd.1 hA)⟩
    · intro m hm hnot
      simp only [Finset.mem_Ioc] at hm hnot
      have hgt : N / d < m := by omega
      have hz : ¬ d * m ≤ N := by
        intro hc
        have : m ≤ N / d := (Nat.le_div_iff_mul_le hd0).mpr (by rwa [mul_comm] at hc)
        omega
      rw [if_neg hz]
      simp
  -- the complex identity with indicator coefficients
  have hid : ∑ d ∈ Finset.Ico A B,
      ((∑ m ∈ Finset.Ioc V (N / A),
          ((if d * m ≤ N then g m else 0 : ℝ) : ℂ) * e ((d : ℝ) * (m : ℝ) * α)) *
        (starRingEnd ℂ) (∑ m ∈ Finset.Ioc V (N / A),
          ((if d * m ≤ N then g m else 0 : ℝ) : ℂ) * e ((d : ℝ) * (m : ℝ) * α)))
      = ∑ m₁ ∈ Finset.Ioc V (N / A), ∑ m₂ ∈ Finset.Ioc V (N / A),
          ((g m₁ * g m₂ : ℝ) : ℂ) *
            ∑ d ∈ (Finset.Ico A B).filter (fun d => d * m₁ ≤ N ∧ d * m₂ ≤ N),
              e ((d : ℝ) * (((m₁ : ℝ) - m₂) * α)) := by
    have hpt : ∀ d ∈ Finset.Ico A B,
        (∑ m ∈ Finset.Ioc V (N / A),
            ((if d * m ≤ N then g m else 0 : ℝ) : ℂ) * e ((d : ℝ) * (m : ℝ) * α)) *
          (starRingEnd ℂ) (∑ m ∈ Finset.Ioc V (N / A),
            ((if d * m ≤ N then g m else 0 : ℝ) : ℂ) * e ((d : ℝ) * (m : ℝ) * α))
        = ∑ m₁ ∈ Finset.Ioc V (N / A), ∑ m₂ ∈ Finset.Ioc V (N / A),
            (if d * m₁ ≤ N ∧ d * m₂ ≤ N then ((g m₁ * g m₂ : ℝ) : ℂ)
              * e ((d : ℝ) * (((m₁ : ℝ) - m₂) * α)) else 0) := by
      intro d _
      rw [map_sum, Finset.sum_mul_sum]
      apply Finset.sum_congr rfl; intro m₁ _
      apply Finset.sum_congr rfl; intro m₂ _
      rw [map_mul, e_conj, Complex.conj_ofReal]
      have h1 : e ((d : ℝ) * (m₁ : ℝ) * α) * e (-((d : ℝ) * (m₂ : ℝ) * α))
          = e ((d : ℝ) * (((m₁ : ℝ) - m₂) * α)) := by
        rw [e_add]; congr 1; ring
      by_cases hc1 : d * m₁ ≤ N
      · by_cases hc2 : d * m₂ ≤ N
        · rw [if_pos hc1, if_pos hc2, if_pos ⟨hc1, hc2⟩]
          push_cast
          calc (g m₁ : ℂ) * e ((d : ℝ) * (m₁ : ℝ) * α)
                * ((g m₂ : ℂ) * e (-((d : ℝ) * (m₂ : ℝ) * α)))
              = ((g m₁ : ℂ) * g m₂)
                * (e ((d : ℝ) * (m₁ : ℝ) * α) * e (-((d : ℝ) * (m₂ : ℝ) * α))) := by ring
            _ = ((g m₁ : ℂ) * g m₂) * e ((d : ℝ) * (((m₁ : ℝ) - m₂) * α)) := by rw [h1]
        · have hcon : ¬ (d * m₁ ≤ N ∧ d * m₂ ≤ N) := fun h => hc2 h.2
          rw [if_pos hc1, if_neg hc2, if_neg hcon]
          push_cast
          ring
      · have hcon : ¬ (d * m₁ ≤ N ∧ d * m₂ ≤ N) := fun h => hc1 h.1
        rw [if_neg hc1, if_neg hcon]
        push_cast
        ring
    rw [Finset.sum_congr rfl hpt]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro m₁ _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro m₂ _
    rw [Finset.mul_sum, Finset.sum_filter]
  -- assemble: real parts + triangle
  have hre : ∑ d ∈ Finset.Ico A B,
      ‖∑ m ∈ Finset.Ioc V (N / d), (g m : ℂ) * e ((d : ℝ) * (m : ℝ) * α)‖ ^ 2
      = (∑ d ∈ Finset.Ico A B,
          ((∑ m ∈ Finset.Ioc V (N / A),
              ((if d * m ≤ N then g m else 0 : ℝ) : ℂ) * e ((d : ℝ) * (m : ℝ) * α)) *
            (starRingEnd ℂ) (∑ m ∈ Finset.Ioc V (N / A),
              ((if d * m ≤ N then g m else 0 : ℝ) : ℂ) * e ((d : ℝ) * (m : ℝ) * α)))).re := by
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro d hd
    rw [← hext d hd, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    exact (Complex.ofReal_re _).symm
  rw [hre, hid]
  calc (∑ m₁ ∈ Finset.Ioc V (N / A), ∑ m₂ ∈ Finset.Ioc V (N / A),
        ((g m₁ * g m₂ : ℝ) : ℂ) *
          ∑ d ∈ (Finset.Ico A B).filter (fun d => d * m₁ ≤ N ∧ d * m₂ ≤ N),
            e ((d : ℝ) * (((m₁ : ℝ) - m₂) * α))).re
      ≤ ‖∑ m₁ ∈ Finset.Ioc V (N / A), ∑ m₂ ∈ Finset.Ioc V (N / A),
          ((g m₁ * g m₂ : ℝ) : ℂ) *
            ∑ d ∈ (Finset.Ico A B).filter (fun d => d * m₁ ≤ N ∧ d * m₂ ≤ N),
              e ((d : ℝ) * (((m₁ : ℝ) - m₂) * α))‖ := Complex.re_le_norm _
    _ ≤ ∑ m₁ ∈ Finset.Ioc V (N / A), ‖∑ m₂ ∈ Finset.Ioc V (N / A),
          ((g m₁ * g m₂ : ℝ) : ℂ) *
            ∑ d ∈ (Finset.Ico A B).filter (fun d => d * m₁ ≤ N ∧ d * m₂ ≤ N),
              e ((d : ℝ) * (((m₁ : ℝ) - m₂) * α))‖ := norm_sum_le _ _
    _ ≤ ∑ m₁ ∈ Finset.Ioc V (N / A), ∑ m₂ ∈ Finset.Ioc V (N / A),
          ‖((g m₁ * g m₂ : ℝ) : ℂ) *
            ∑ d ∈ (Finset.Ico A B).filter (fun d => d * m₁ ≤ N ∧ d * m₂ ≤ N),
              e ((d : ℝ) * (((m₁ : ℝ) - m₂) * α))‖ :=
        Finset.sum_le_sum (fun m₁ _ => norm_sum_le _ _)
    _ = ∑ m₁ ∈ Finset.Ioc V (N / A), ∑ m₂ ∈ Finset.Ioc V (N / A),
          |g m₁| * |g m₂| *
            ‖∑ d ∈ (Finset.Ico A B).filter (fun d => d * m₁ ≤ N ∧ d * m₂ ≤ N),
              e ((d : ℝ) * (((m₁ : ℝ) - m₂) * α))‖ := by
        apply Finset.sum_congr rfl; intro m₁ _
        apply Finset.sum_congr rfl; intro m₂ _
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]

/-- **The S₄-block second moment**: the full hyperbola-restricted second moment through
    the workhorse chain. -/
lemma S4_block_second_moment (a q : ℕ) (hq : 2 ≤ q) (ha : Nat.Coprime a q) (α : ℝ)
    (hα : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2)
    (g : ℕ → ℝ) (G : ℝ) (hg0 : ∀ m, 0 ≤ g m) (hgG : ∀ m, g m ≤ G)
    (N A B V : ℕ) (hA : 0 < A) :
    ∑ d ∈ Finset.Ico A B,
      ‖∑ m ∈ Finset.Ioc V (N / d), (g m : ℂ) * e ((d : ℝ) * (m : ℝ) * α)‖ ^ 2
      ≤ G ^ 2 * (((N / A : ℕ) : ℝ) + 1) *
          (((B - A : ℕ) : ℝ) + 2 * ((((N / A : ℕ)) / (q / 2) + 1 : ℕ) : ℝ)
            * (2 * ((B - A : ℕ) : ℝ) + 4 * q * (1 + Real.log (2 * q)))) := by
  have hG0 : 0 ≤ G := le_trans (hg0 0) (hgG 0)
  set F : ℤ → ℝ := fun h =>
    (if (h : ℝ) * α - round ((h : ℝ) * α) = 0 then ((B - A : ℕ) : ℝ)
     else min ((B - A : ℕ) : ℝ) (1 / (2 * |(h : ℝ) * α - round ((h : ℝ) * α)|))) with hF
  have hF0 : ∀ h, 0 ≤ F h := by
    intro h
    rw [hF]
    dsimp only
    split
    · positivity
    · exact le_min (by positivity) (by positivity)
  -- per-pair bound
  have hpair : ∀ m₁ ∈ Finset.Ioc V (N / A), ∀ m₂ ∈ Finset.Ioc V (N / A),
      |g m₁| * |g m₂| *
        ‖∑ d ∈ (Finset.Ico A B).filter (fun d => d * m₁ ≤ N ∧ d * m₂ ≤ N),
          e ((d : ℝ) * (((m₁ : ℝ) - m₂) * α))‖
      ≤ G * G * F ((m₁ : ℤ) - m₂) := by
    intro m₁ hm₁ m₂ hm₂
    simp only [Finset.mem_Ioc] at hm₁ hm₂
    have hcapF : ‖∑ d ∈ (Finset.Ico A B).filter (fun d => d * m₁ ≤ N ∧ d * m₂ ≤ N),
        e ((d : ℝ) * (((m₁ : ℝ) - m₂) * α))‖ ≤ F ((m₁ : ℤ) - m₂) := by
      have h1 := filtered_exp_sum_cap (((m₁ : ℝ) - m₂) * α) N A B m₁ m₂
        (by omega) (by omega)
      have hcast : ((((m₁ : ℤ) - m₂) : ℤ) : ℝ) * α = ((m₁ : ℝ) - m₂) * α := by
        push_cast
        ring
      rw [hF]
      dsimp only
      rw [hcast]
      exact h1
    have hg1 : |g m₁| ≤ G := by rw [abs_of_nonneg (hg0 m₁)]; exact hgG m₁
    have hg2 : |g m₂| ≤ G := by rw [abs_of_nonneg (hg0 m₂)]; exact hgG m₂
    apply mul_le_mul _ hcapF (norm_nonneg _) (by positivity)
    exact mul_le_mul hg1 hg2 (abs_nonneg _) hG0
  -- extend the double sum to squares of ranges
  have hIoc_sub : Finset.Ioc V (N / A) ⊆ Finset.range (N / A + 1) := by
    intro m hm
    simp only [Finset.mem_Ioc] at hm
    simp only [Finset.mem_range]
    omega
  calc ∑ d ∈ Finset.Ico A B,
      ‖∑ m ∈ Finset.Ioc V (N / d), (g m : ℂ) * e ((d : ℝ) * (m : ℝ) * α)‖ ^ 2
      ≤ ∑ m₁ ∈ Finset.Ioc V (N / A), ∑ m₂ ∈ Finset.Ioc V (N / A),
          |g m₁| * |g m₂| *
            ‖∑ d ∈ (Finset.Ico A B).filter (fun d => d * m₁ ≤ N ∧ d * m₂ ≤ N),
              e ((d : ℝ) * (((m₁ : ℝ) - m₂) * α))‖ :=
        hyperbola_second_moment_expand g α N A B V hA
    _ ≤ ∑ m₁ ∈ Finset.Ioc V (N / A), ∑ m₂ ∈ Finset.Ioc V (N / A),
          G * G * F ((m₁ : ℤ) - m₂) := by
        apply Finset.sum_le_sum
        intro m₁ hm₁
        exact Finset.sum_le_sum (fun m₂ hm₂ => hpair m₁ hm₁ m₂ hm₂)
    _ ≤ ∑ m₁ ∈ Finset.Ioc V (N / A), ∑ m₂ ∈ Finset.range (N / A + 1),
          G * G * F ((m₁ : ℤ) - m₂) := by
        apply Finset.sum_le_sum
        intro m₁ _
        apply Finset.sum_le_sum_of_subset_of_nonneg hIoc_sub
        intro m₂ _ _
        positivity
    _ ≤ ∑ m₁ ∈ Finset.range (N / A + 1), ∑ m₂ ∈ Finset.range (N / A + 1),
          G * G * F ((m₁ : ℤ) - m₂) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hIoc_sub
        intro m₁ _ _
        exact Finset.sum_nonneg (fun m₂ _ => by positivity)
    _ = G * G * ∑ m₁ ∈ Finset.range (N / A + 1), ∑ m₂ ∈ Finset.range (N / A + 1),
          F ((m₁ : ℤ) - m₂) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m₁ _
        rw [Finset.mul_sum]
    _ ≤ G * G * (((N / A + 1 : ℕ) : ℝ) *
          ∑ h ∈ Finset.Icc (-(N / A + 1 : ℕ) + 1 : ℤ) ((N / A + 1 : ℕ) - 1 : ℤ), F h) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact_mod_cast diff_count_le F hF0 (N / A + 1)
    _ ≤ G * G * (((N / A + 1 : ℕ) : ℝ) *
          (((B - A : ℕ) : ℝ) + 2 * ((((N / A + 1 - 1 : ℕ)) / (q / 2) + 1 : ℕ) : ℝ)
            * (2 * ((B - A : ℕ) : ℝ) + 4 * q * (1 + Real.log (2 * q))))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have h5 := cap_symmetric_sum_le a q hq ha α hα ((B - A : ℕ) : ℝ)
          (by positivity) (N / A + 1)
        rw [hF]
        exact_mod_cast h5
    _ = G ^ 2 * (((N / A : ℕ) : ℝ) + 1) *
          (((B - A : ℕ) : ℝ) + 2 * ((((N / A : ℕ)) / (q / 2) + 1 : ℕ) : ℝ)
            * (2 * ((B - A : ℕ) : ℝ) + 4 * q * (1 + Real.log (2 * q)))) := by
        rw [Nat.add_sub_cancel]
        push_cast
        ring

/-- **The variance quartic step**: on any interval where `‖S‖ ≤ C`, the fourth moment is
    controlled by `C²` times the second moment. (The per-arc core of
    `∫_𝔪 |S|⁴ ≤ (sup_𝔪|S|)²·∫|S|²`; the arc decomposition supplies the intervals.) -/
lemma quartic_le_sq_mul_sq (S : ℝ → ℂ) (C : ℝ) (a b : ℝ) (hab : a ≤ b)
    (hbound : ∀ α ∈ Set.Icc a b, ‖S α‖ ≤ C)
    (hint2 : IntervalIntegrable (fun α => ‖S α‖ ^ 2) MeasureTheory.volume a b)
    (hint4 : IntervalIntegrable (fun α => ‖S α‖ ^ 4) MeasureTheory.volume a b) :
    ∫ α in a..b, ‖S α‖ ^ 4 ≤ C ^ 2 * ∫ α in a..b, ‖S α‖ ^ 2 := by
  have hC0 : 0 ≤ C := by
    rcases eq_or_lt_of_le hab with h | h
    · -- degenerate interval: both integrals vanish; C ≥ 0 not needed, handle below
      exact le_trans (norm_nonneg (S a)) (hbound a (by constructor <;> simp [h.le]))
    · exact le_trans (norm_nonneg (S a)) (hbound a ⟨le_refl a, hab⟩)
  have hpt : ∀ α ∈ Set.Icc a b, ‖S α‖ ^ 4 ≤ C ^ 2 * ‖S α‖ ^ 2 := by
    intro α hα
    have h1 : ‖S α‖ ≤ C := hbound α hα
    have h2 : ‖S α‖ ^ 2 ≤ C ^ 2 := by
      apply pow_le_pow_left₀ (norm_nonneg _) h1
    calc ‖S α‖ ^ 4 = ‖S α‖ ^ 2 * ‖S α‖ ^ 2 := by ring
      _ ≤ C ^ 2 * ‖S α‖ ^ 2 :=
        mul_le_mul_of_nonneg_right h2 (by positivity)
  calc ∫ α in a..b, ‖S α‖ ^ 4
      ≤ ∫ α in a..b, C ^ 2 * ‖S α‖ ^ 2 := by
        apply intervalIntegral.integral_mono_on hab hint4 (hint2.const_mul (C ^ 2))
        exact hpt
    _ = C ^ 2 * ∫ α in a..b, ‖S α‖ ^ 2 := intervalIntegral.integral_const_mul _ _

end MinSum
end Principia.Common.Goldbach
