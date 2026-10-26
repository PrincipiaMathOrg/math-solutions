import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# MathDB #331705 — a starlike domain with a non-starlike Cassinian ball

Write-up: `mathdb-open-problems/problems/331705/solution.tex`, collaborator branch
`mathdb-results` of `antoshashakov/Principia-Math-In-Progress`.
Source: **Conjecture 4.7** — if a domain `G` is starlike with respect to `x`, then every
Cassinian ball `B_{c_G}(x,r) = {y ∈ G : c_G(x,y) < r}` is starlike with respect to `x`,
where

`c_G(x,y) = sup_{p ∈ ∂G} ‖x−y‖ / (‖x−p‖ ‖p−y‖)`.

The counterexample, in `ℂ = ℝ²`:  `K = {w : 1 ≤ re w, 4|im w| ≤ re w − 1}`,
`G = ball 0 10 \ K`.  Then `G` is a bounded domain, strictly starlike about `0`, but
`B_{c_G}(0, 5/4)` is not: with `y = 4+4i` and `z = 1+i = y/4`, the point `y` lies in the
ball while `z` — on the segment `[0,y]` — does not.

## Why this row was mis-deferred

Deferred 2026-09-16 as "the polynomial inequalities are easy, the geometry is not".  The
geometry is one boundary inclusion, `∂G ⊆ {‖p‖ = 10} ∪ ∂K`, proved by four cases on where
`p` sits; and the distances are attained at the single boundary point `1` (i.e. `(1,0)`).

## What is proved

* `starlike` — `[0,w) ⊆ G` for every `w ∈ closure G`, the write-up's strict starlikeness.
* `frontier_subset` — `∂G ⊆ {p : ‖p‖ = 10} ∪ {p : 1 ≤ re p ∧ 4|im p| = re p − 1}`.
* `one_mem_frontier` — `1 ∈ ∂G`, so the supremum is over a nonempty set.
* `poly_four`, `poly_one` — the write-up's completions of squares:
  `P₄(t) ≥ 25` and `P₁(t) ≥ 1` for `t ≥ 0`, with equality only at `t = 0`.
* `cass_y_le`, `cass_z_ge` — `c_G(0,y) ≤ 4√2/5 < 5/4 ≤ √2 ≤ c_G(0,z)`.
* `not_conj` — hence the Cassinian ball of radius `5/4` about `0` is not starlike.

Values checked in `Campaigns/MathDB-Formalization/verify_331705.py`, which also computes
the supremum over the whole boundary numerically and matches `4√2/5` and `√2` exactly.
-/

namespace Principia.MathDB.P331705

open Complex

/-- The removed wedge `K = {1 ≤ re w, 4|im w| ≤ re w − 1}`. -/
def K : Set ℂ := {w : ℂ | 1 ≤ w.re ∧ 4 * |w.im| ≤ w.re - 1}

/-- The domain `G = B(0,10) \ K`. -/
def G : Set ℂ := {w : ℂ | ‖w‖ < 10} \ K

theorem G_open : IsOpen G := by
  have h1 : IsOpen {w : ℂ | ‖w‖ < 10} := isOpen_lt continuous_norm continuous_const
  have h2 : IsClosed K := by
    have ha : Continuous fun w : ℂ => w.re := Complex.continuous_re
    have hb : Continuous fun w : ℂ => 4 * |w.im| := by
      exact (continuous_const.mul (Complex.continuous_im.abs))
    exact (isClosed_le continuous_const ha).inter (isClosed_le hb (ha.sub continuous_const))
  exact h1.inter h2.isOpen_compl

theorem mem_G {w : ℂ} : w ∈ G ↔ ‖w‖ < 10 ∧ ¬ (1 ≤ w.re ∧ 4 * |w.im| ≤ w.re - 1) := by
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, h2⟩

/-! ### `G` is strictly starlike about `0` -/

/-- **The write-up's starlikeness computation**: scaling a point of `closure G` strictly
towards `0` lands in `G`. -/
theorem starlike {w : ℂ} (hw : ‖w‖ ≤ 10) (hK : ¬ (1 < w.re ∧ 4 * |w.im| < w.re - 1))
    {tau : ℝ} (h0 : 0 ≤ tau) (h1 : tau < 1) : (tau : ℂ) * w ∈ G := by
  have hnorm : ‖(tau : ℂ) * w‖ < 10 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]
    rcases eq_or_lt_of_le h0 with h | h
    · rw [← h]; simp
    · calc tau * ‖w‖ ≤ tau * 10 := by
            exact mul_le_mul_of_nonneg_left hw h0
        _ < 1 * 10 := by nlinarith
        _ = 10 := one_mul 10
  refine ⟨hnorm, ?_⟩
  rintro ⟨hre, him⟩
  -- `(tau * w).re = tau * w.re` and `(tau * w).im = tau * w.im`
  have hre' : ((tau : ℂ) * w).re = tau * w.re := by simp
  have him' : ((tau : ℂ) * w).im = tau * w.im := by simp
  rw [hre'] at hre
  rw [him', abs_mul, abs_of_nonneg h0] at him
  -- so `1 ≤ tau * re w`, hence `re w > 1` and `tau > 0`
  have htau : 0 < tau := by
    rcases eq_or_lt_of_le h0 with h | h
    · exfalso; rw [← h] at hre; simp at hre; linarith
    · exact h
  have hwre : 1 < w.re := by nlinarith [hre, htau, h1]
  -- the wedge condition transported back
  have hstep : 4 * |w.im| < w.re - 1 := by
    have h4 : 4 * (tau * |w.im|) ≤ tau * w.re - 1 := by linarith [him]
    have : tau * (4 * |w.im|) ≤ tau * w.re - 1 := by linarith [h4]
    have hlt : tau * (4 * |w.im|) < tau * (w.re - 1) := by
      have : tau * w.re - 1 < tau * w.re - tau := by linarith
      linarith [this, ‹tau * (4 * |w.im|) ≤ tau * w.re - 1›]
    exact lt_of_mul_lt_mul_left (by linarith [hlt]) h0
  exact hK ⟨hwre, hstep⟩


/-! ### The boundary of `G` -/

/-- The open wedge interior, which is disjoint from `G`. -/
def Kint : Set ℂ := {w : ℂ | 1 < w.re ∧ 4 * |w.im| < w.re - 1}

theorem Kint_open : IsOpen Kint := by
  have ha : Continuous fun w : ℂ => w.re := Complex.continuous_re
  have hb : Continuous fun w : ℂ => 4 * |w.im| := continuous_const.mul Complex.continuous_im.abs
  exact (isOpen_lt continuous_const ha).inter (isOpen_lt hb (ha.sub continuous_const))

theorem Kint_disjoint {w : ℂ} (hw : w ∈ Kint) : w ∉ G := by
  rintro ⟨-, hnk⟩
  exact hnk ⟨le_of_lt hw.1, le_of_lt hw.2⟩

theorem closure_le_ten {p : ℂ} (hp : p ∈ closure G) : ‖p‖ ≤ 10 := by
  have hsub : closure G ⊆ {w : ℂ | ‖w‖ ≤ 10} :=
    closure_minimal (fun w hw => by
      have hlt : ‖w‖ < 10 := hw.1
      exact le_of_lt hlt)
      (isClosed_le continuous_norm continuous_const)
  exact hsub hp

/-- **`∂G` lies on the circle or on the two rays.**  Four cases on where `p` sits: outside
the disc it is not in `closure G`; inside the disc and off `K` it is in the open set `G`;
inside the disc and in the OPEN wedge it has a neighbourhood missing `G`; what is left is
the circle and `4|im p| = re p − 1`. -/
theorem frontier_subset {p : ℂ} (hp : p ∈ frontier G) :
    ‖p‖ = 10 ∨ (1 ≤ p.re ∧ 4 * |p.im| = p.re - 1) := by
  have hcl : p ∈ closure G := hp.1
  have hnG : p ∉ G := by
    have := hp.2
    rwa [G_open.interior_eq] at this
  have hle : ‖p‖ ≤ 10 := closure_le_ten hcl
  by_cases h10 : ‖p‖ = 10
  · exact Or.inl h10
  · right
    have hlt : ‖p‖ < 10 := lt_of_le_of_ne hle h10
    have hK : 1 ≤ p.re ∧ 4 * |p.im| ≤ p.re - 1 := by
      by_contra hc
      exact hnG ⟨hlt, hc⟩
    refine ⟨hK.1, ?_⟩
    by_contra hne
    have hstrict : 4 * |p.im| < p.re - 1 := lt_of_le_of_ne hK.2 hne
    have hre1 : 1 < p.re := by
      have h0 : 0 ≤ 4 * |p.im| := by positivity
      linarith
    obtain ⟨w, hwU, hwG⟩ := (mem_closure_iff.1 hcl) Kint Kint_open ⟨hre1, hstrict⟩
    exact Kint_disjoint hwU hwG

/-- `1` is a boundary point: it lies in `K`, and `1 - δ` lies in `G` for small `δ > 0`. -/
theorem one_mem_frontier : (1 : ℂ) ∈ frontier G := by
  rw [G_open.frontier_eq]
  constructor
  · rw [mem_closure_iff_nhds]
    intro s hs
    rw [Metric.mem_nhds_iff] at hs
    obtain ⟨eps, heps, hball⟩ := hs
    set d : ℝ := min (eps / 2) (1 / 2) with hd
    have hd0 : 0 < d := lt_min (by linarith) (by norm_num)
    have hd1 : d ≤ 1 / 2 := min_le_right _ _
    have hd2 : d ≤ eps / 2 := min_le_left _ _
    refine ⟨((1 - d : ℝ) : ℂ), hball ?_, ?_⟩
    · rw [Metric.mem_ball, Complex.dist_eq]
      have he : ((1 - d : ℝ) : ℂ) - 1 = ((-d : ℝ) : ℂ) := by push_cast; ring
      rw [he, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_nonneg hd0.le]
      linarith
    · refine ⟨?_, ?_⟩
      · show ‖((1 - d : ℝ) : ℂ)‖ < 10
        rw [Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - d)]
        linarith
      · rintro ⟨hre, -⟩
        rw [Complex.ofReal_re] at hre
        linarith
  · rintro ⟨-, hnk⟩
    exact hnk ⟨by norm_num, by norm_num⟩

/-! ### The two polynomial bounds (the write-up's completions of squares) -/

/-- `P₄(t) ≥ 25` for `t ≥ 0`: `P₄(t) − 25 = 42t + t²[(289/256)(t − 48/17)² + 21/8]`. -/
theorem poly_four {t : ℝ} (ht : 0 ≤ t) :
    25 ≤ ((1 + t) ^ 2 + t ^ 2 / 16) * ((t - 3) ^ 2 + (t / 4 - 4) ^ 2) := by
  nlinarith [ht, sq_nonneg t, sq_nonneg (t - 48 / 17),
    mul_nonneg (sq_nonneg t) (sq_nonneg (t - 48 / 17))]

/-- `P₁(t) ≥ 1` for `t ≥ 0`:
`P₁(t) − 1 = (3/2)t + (9/8)t² + (51/32)t³ + (289/256)t⁴`. -/
theorem poly_one {t : ℝ} (ht : 0 ≤ t) :
    1 ≤ ((1 + t) ^ 2 + t ^ 2 / 16) * (t ^ 2 + (t / 4 - 1) ^ 2) := by
  nlinarith [ht, sq_nonneg t, mul_nonneg ht (sq_nonneg t),
    mul_nonneg (sq_nonneg t) (sq_nonneg t)]


/-! ### The Cassinian distances -/

theorem norm_sq_eq (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring

/-- The witness `y = 4 + 4i`. -/
noncomputable def yy : ℂ := 4 + 4 * Complex.I

/-- The point `z = 1 + i = y/4`, on the segment from `0` to `y`. -/
noncomputable def zz : ℂ := 1 + Complex.I

theorem yy_re : yy.re = 4 := by simp [yy]
theorem yy_im : yy.im = 4 := by simp [yy]
theorem zz_re : zz.re = 1 := by simp [zz]
theorem zz_im : zz.im = 1 := by simp [zz]

theorem norm_yy : ‖yy‖ = 4 * Real.sqrt 2 := by
  have h : ‖yy‖ ^ 2 = 32 := by rw [norm_sq_eq, yy_re, yy_im]; norm_num
  have h2 : (4 * Real.sqrt 2) ^ 2 = 32 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]; norm_num
  have hn : 0 ≤ ‖yy‖ := norm_nonneg _
  have hm : 0 ≤ 4 * Real.sqrt 2 := by positivity
  nlinarith [h, h2, hn, hm]

theorem norm_zz : ‖zz‖ = Real.sqrt 2 := by
  have h : ‖zz‖ ^ 2 = 2 := by rw [norm_sq_eq, zz_re, zz_im]; norm_num
  have h2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hn : 0 ≤ ‖zz‖ := norm_nonneg _
  have hm : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  nlinarith [h, h2, hn, hm]

theorem sqrt_two_lt : Real.sqrt 2 < 3 / 2 := by
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]

theorem sqrt_two_gt : 5 / 4 < Real.sqrt 2 := by
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]

/-- **The product `‖p‖·‖p−w‖` is bounded below on `∂G`**, for `w = a + ai` with `a > 0`,
by the square root of the node polynomial at `t = re p − 1`. -/
theorem prod_lower {a : ℝ} (ha : 0 < a) {w : ℂ} (hwre : w.re = a) (hwim : w.im = a)
    {p : ℂ} (hre : 1 ≤ p.re) (him : 4 * |p.im| = p.re - 1) :
    ((1 + (p.re - 1)) ^ 2 + (p.re - 1) ^ 2 / 16)
        * ((1 + (p.re - 1) - a) ^ 2 + ((p.re - 1) / 4 - a) ^ 2)
      ≤ ‖p‖ ^ 2 * ‖p - w‖ ^ 2 := by
  set t := p.re - 1 with htdef
  have ht : 0 ≤ t := by linarith
  have himt : |p.im| = t / 4 := by linarith [him]
  have hsq : p.im ^ 2 = (t / 4) ^ 2 := by
    rw [← sq_abs, himt]
  have hnp : ‖p‖ ^ 2 = (1 + t) ^ 2 + t ^ 2 / 16 := by
    rw [norm_sq_eq, hsq]
    have : p.re = 1 + t := by linarith
    rw [this]; ring
  have hdre : (p - w).re = 1 + t - a := by
    rw [Complex.sub_re, hwre]; linarith
  have hdim : (p - w).im = p.im - a := by rw [Complex.sub_im, hwim]
  have hnd : ‖p - w‖ ^ 2 = (1 + t - a) ^ 2 + (p.im - a) ^ 2 := by
    rw [norm_sq_eq, hdre, hdim]
  -- `(p.im − a)² ≥ (t/4 − a)²`, with equality on the upper ray
  have hkey : (t / 4 - a) ^ 2 ≤ (p.im - a) ^ 2 := by
    rcases abs_eq (by positivity : (0:ℝ) ≤ t / 4) |>.1 himt with h | h
    · rw [h]
    · rw [h]; nlinarith [ht, ha]
  rw [hnp, hnd]
  have hpos : (0:ℝ) ≤ (1 + t) ^ 2 + t ^ 2 / 16 := by positivity
  nlinarith [hkey, hpos]

/-- The Cassinian metric of `G`, as the supremum over the boundary. -/
noncomputable def cass (x y : ℂ) : ℝ :=
  ⨆ p : frontier G, ‖x - y‖ / (‖x - (p : ℂ)‖ * ‖(p : ℂ) - y‖)


theorem cass_apply (x y : ℂ) :
    cass x y = ⨆ p : frontier G, ‖x - y‖ / (‖x - (p : ℂ)‖ * ‖(p : ℂ) - y‖) := rfl

instance : Nonempty (frontier G) := ⟨⟨1, one_mem_frontier⟩⟩

/-- **The Cassinian quotient at `y` is at most `4√2/5` at every boundary point.** -/
theorem bound_y {p : ℂ} (hp : p ∈ frontier G) :
    ‖(0:ℂ) - yy‖ / (‖(0:ℂ) - p‖ * ‖p - yy‖) ≤ 4 * Real.sqrt 2 / 5 := by
  have h0y : ‖(0:ℂ) - yy‖ = 4 * Real.sqrt 2 := by rw [zero_sub, norm_neg, norm_yy]
  have h0p : ‖(0:ℂ) - p‖ = ‖p‖ := by rw [zero_sub, norm_neg]
  have hs2 : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hprod : (5:ℝ) ≤ ‖p‖ * ‖p - yy‖ := by
    rcases frontier_subset hp with hc | ⟨hre, him⟩
    · -- on the circle: ‖p−y‖ ≥ ‖p‖ − ‖y‖ = 10 − 4√2
      have hd : ‖p‖ - ‖yy‖ ≤ ‖p - yy‖ := norm_sub_norm_le _ _
      rw [hc, norm_yy] at hd
      rw [hc]
      have h32 : Real.sqrt 2 < 3 / 2 := sqrt_two_lt
      nlinarith [hd, h32, norm_nonneg (p - yy)]
    · have hpl := prod_lower (by norm_num : (0:ℝ) < 4) yy_re yy_im hre him
      have hp4 := poly_four (by linarith : (0:ℝ) ≤ p.re - 1)
      have hcast : ((1 + (p.re - 1)) ^ 2 + (p.re - 1) ^ 2 / 16)
          * ((1 + (p.re - 1) - 4) ^ 2 + ((p.re - 1) / 4 - 4) ^ 2)
          = ((1 + (p.re - 1)) ^ 2 + (p.re - 1) ^ 2 / 16)
            * (((p.re - 1) - 3) ^ 2 + ((p.re - 1) / 4 - 4) ^ 2) := by ring
      rw [hcast] at hpl
      have h25 : (25:ℝ) ≤ ‖p‖ ^ 2 * ‖p - yy‖ ^ 2 := le_trans hp4 hpl
      have hnn : (0:ℝ) ≤ ‖p‖ * ‖p - yy‖ := by positivity
      nlinarith [h25, hnn]
  rw [h0y, h0p]
  rw [div_le_div_iff₀ (by nlinarith [hprod]) (by norm_num : (0:ℝ) < 5)]
  nlinarith [hprod, hs2]

/-- **The Cassinian quotient at `z` is at most `√2` at every boundary point.** -/
theorem bound_z {p : ℂ} (hp : p ∈ frontier G) :
    ‖(0:ℂ) - zz‖ / (‖(0:ℂ) - p‖ * ‖p - zz‖) ≤ Real.sqrt 2 := by
  have h0z : ‖(0:ℂ) - zz‖ = Real.sqrt 2 := by rw [zero_sub, norm_neg, norm_zz]
  have h0p : ‖(0:ℂ) - p‖ = ‖p‖ := by rw [zero_sub, norm_neg]
  have hs2 : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hprod : (1:ℝ) ≤ ‖p‖ * ‖p - zz‖ := by
    rcases frontier_subset hp with hc | ⟨hre, him⟩
    · have hd : ‖p‖ - ‖zz‖ ≤ ‖p - zz‖ := norm_sub_norm_le _ _
      rw [hc, norm_zz] at hd
      rw [hc]
      have h32 : Real.sqrt 2 < 3 / 2 := sqrt_two_lt
      nlinarith [hd, h32, norm_nonneg (p - zz)]
    · have hpl := prod_lower (by norm_num : (0:ℝ) < 1) zz_re zz_im hre him
      have hp1 := poly_one (by linarith : (0:ℝ) ≤ p.re - 1)
      have hcast : ((1 + (p.re - 1)) ^ 2 + (p.re - 1) ^ 2 / 16)
          * ((1 + (p.re - 1) - 1) ^ 2 + ((p.re - 1) / 4 - 1) ^ 2)
          = ((1 + (p.re - 1)) ^ 2 + (p.re - 1) ^ 2 / 16)
            * ((p.re - 1) ^ 2 + ((p.re - 1) / 4 - 1) ^ 2) := by ring
      rw [hcast] at hpl
      have h1 : (1:ℝ) ≤ ‖p‖ ^ 2 * ‖p - zz‖ ^ 2 := le_trans hp1 hpl
      have hnn : (0:ℝ) ≤ ‖p‖ * ‖p - zz‖ := by positivity
      nlinarith [h1, hnn]
  rw [h0z, h0p]
  rw [div_le_iff₀ (by nlinarith [hprod])]
  nlinarith [hprod, hs2]

theorem cass_y_le : cass 0 yy ≤ 4 * Real.sqrt 2 / 5 :=
  ciSup_le (fun p => bound_y p.2)

theorem bddAbove_z :
    BddAbove (Set.range fun p : frontier G =>
      ‖(0:ℂ) - zz‖ / (‖(0:ℂ) - (p : ℂ)‖ * ‖(p : ℂ) - zz‖)) := by
  refine ⟨Real.sqrt 2, ?_⟩
  rintro v ⟨p, rfl⟩
  exact bound_z p.2

/-- **`c_G(0,z) ≥ √2`**, attained at the boundary point `1`. -/
theorem cass_z_ge : Real.sqrt 2 ≤ cass 0 zz := by
  have hval : ‖(0:ℂ) - zz‖ / (‖(0:ℂ) - (1:ℂ)‖ * ‖(1:ℂ) - zz‖) = Real.sqrt 2 := by
    have h1 : ‖(0:ℂ) - (1:ℂ)‖ = 1 := by simp
    have h2 : (1:ℂ) - zz = -Complex.I := by rw [zz]; ring
    have h3 : ‖(1:ℂ) - zz‖ = 1 := by rw [h2, norm_neg, Complex.norm_I]
    rw [zero_sub, norm_neg, norm_zz, h1, h3]
    norm_num
  have := le_ciSup bddAbove_z (⟨1, one_mem_frontier⟩ : frontier G)
  rw [hval] at this
  exact this

/-! ### The refutation -/

theorem yy_mem : yy ∈ G := by
  refine ⟨?_, ?_⟩
  · show ‖yy‖ < 10
    rw [norm_yy]; nlinarith [sqrt_two_lt, Real.sqrt_nonneg 2]
  · rintro ⟨-, h⟩
    rw [yy_re, yy_im] at h
    norm_num at h

theorem zz_mem : zz ∈ G := by
  refine ⟨?_, ?_⟩
  · show ‖zz‖ < 10
    rw [norm_zz]; nlinarith [sqrt_two_lt, Real.sqrt_nonneg 2]
  · rintro ⟨-, h⟩
    rw [zz_re, zz_im] at h
    norm_num at h

theorem zz_on_segment : zz = ((1:ℝ)/4 : ℂ) * yy := by
  rw [zz, yy]; push_cast; ring

/-- **Conjecture 4.7 is FALSE.**  `G` is strictly starlike about `0`, `y ∈ B_{c_G}(0,5/4)`,
and `z = y/4` lies on the segment `[0,y]` — yet `z ∉ B_{c_G}(0,5/4)`.  So the Cassinian ball
is not starlike about `0`. -/
theorem not_conj :
    yy ∈ G ∧ zz ∈ G ∧ zz = ((1:ℝ)/4 : ℂ) * yy ∧
      cass 0 yy < 5 / 4 ∧ ¬ (cass 0 zz < 5 / 4) := by
  refine ⟨yy_mem, zz_mem, zz_on_segment, ?_, ?_⟩
  · have h := cass_y_le
    nlinarith [h, sqrt_two_lt, Real.sqrt_nonneg 2]
  · intro hlt
    have h := cass_z_ge
    nlinarith [h, hlt, sqrt_two_gt]

end Principia.MathDB.P331705
