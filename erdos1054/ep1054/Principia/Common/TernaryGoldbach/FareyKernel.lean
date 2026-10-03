/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.MajorFromPlatt

set_option autoImplicit false

/-!
# The Farey decomposition and the kernel truncation loss

Two of the five slots left in `MajorPlatt.cite_Helfgott_weighted_of_platt_chain`: Link M1
(`FareyDecomposition`) is **discharged here as a theorem with no hypotheses**, and Link M3
(`KernelTailBound (1/10⁵)`) is **measured TRUE** and reduced to three named obligations.

## M1, discharged — `fareyDecomposition_holds`

`majorIntegral H P Q = ∑_{q ≤ P} arcSum H q Q` at any cutoffs with `1 ≤ P` and `2P < Q+1`, hence at
`MajorPlatt.Pcut`/`Qcut` via `cutoff_separation`. Pure measure theory, and the docstring of
`MajorFromPlatt.FareyDecomposition` was right that the endpoint bookkeeping is the work: the major
set is `Ioc 0 1 ∩ MajorArcs P Q`, but the modulus-`1` window straddles `0`, so summing over reduced
residues in `[0,q)` matches the major set only after the period is **shifted**. The proof therefore
does not reason about `(0,1]` at all. It writes the integrand as
`Set.indicator (MajorArcs P Q) (kern H)`, proves that function `1`-periodic
(`kernIndicator_periodic`, from `Spine.kern_periodic` for the values and `majorArcs_add_intCast` for
the support), and moves the period to `(-w₁, 1-w₁)` with
`Function.Periodic.intervalIntegral_add_eq`. Inside *that* period the major set is exactly the union
of the reduced windows, up to the two endpoints, which are Lebesgue-null.

Two further things the docstring predicted and that turned out otherwise:

* **The reduction to lowest terms is not needed as a rational-arithmetic step.** `MajorArcs`
  quantifies over *all* `a : ℤ`, so a window about a non-reduced `a/q` has to be absorbed into the
  wider window of its reduced form. But `2P < Q+1` forces `2·w₁ ≤ 1/q`, which pins the numerator
  into `[0, q)` **before** any reduction (`exists_win_of_mem_majorArcs`), after which the reduction
  is a bare `Nat.gcd` division. No `ℚ`, no `Rat.den`.
* **`2P < Q+1` is spent twice, not once.** Once as Farey separation (`win_disjoint`: distinct
  reduced anchors are `≥ 1/(qq')` apart while the windows total `(q+q')/(qq'(Q+1))`), and once
  as the numerator pin above. `cutoff_separation` supplies both.

## M3, measured and reduced — `kernelTailBound_std`

`KernelTailBound (1/10⁵)` is **TRUE, by a factor of 197.6** on the crude chargeable bound, and the
`24.6×` figure in `MajorFromPlatt`'s Link-M3 docstring is about a different comparison
(`100·errScale`) and must not be read as a threat to `cK`. The numbers, recomputed two ways, are in
the Link-M3 section below; the chain proved here lands at `1.25·10⁻⁷·H²`, inside `cK = 10⁻⁵` by
`80×`. What is left are three obligations — `FullCircleTriple` (orthogonality),
`WindowTailGeom (1/8)` (the `|U(β)| ≤ 1/(2‖β‖)` tail) and `LocalTermWeightSum (10⁶)` (a finite
arithmetic sum) — each of which *constrains* its constant, with the certificate proved:
`windowTailGeom_nonneg`, `localTermWeightSum_one_le`, `kernelTailBound_nonneg`.

## What is NOT claimed

Nothing here proves any part of ternary Goldbach. `FullCircleTriple`, `WindowTailGeom` and
`LocalTermWeightSum` are `def … : Prop` and unproved; `cite_Helfgott_weighted_of_kernel_links`
carries them, together with `PlattGRH`, `WindowApproxUnder`, `MinorSupBound`, and the three slots
already discharged in sibling modules.
-/

namespace Principia.Common.TernaryGoldbach.FareyKernel

open MeasureTheory Principia.Common.Goldbach
open Principia.Common.TernaryGoldbach.Spine
open Principia.Common.TernaryGoldbach.MajorPlatt

/-! ## The Farey windows as sets -/

/-- The reduced residues mod `q`, indexed **exactly** as `MajorPlatt.arcSum` indexes its sum, so
that no re-indexing is needed anywhere below. `red 1 = {0}`. -/
def red (q : ℕ) : Finset ℕ := (Finset.range q).filter (fun a => Nat.gcd a q = 1)

/-- The Farey window of `a/q` at level `Q` — literally one of the closed balls whose union is
`Goldbach.MajorArcs P Q`. -/
noncomputable def win (q Q a : ℕ) : Set ℝ :=
  Metric.closedBall ((a : ℝ) / (q : ℝ)) (halfWidth q Q)

theorem mem_red_iff {q a : ℕ} : a ∈ red q ↔ a < q ∧ Nat.gcd a q = 1 := by
  simp [red, Finset.mem_filter, Finset.mem_range]

theorem measurableSet_win (q Q a : ℕ) : MeasurableSet (win q Q a) :=
  measurableSet_closedBall

theorem halfWidth_pos {q Q : ℕ} (hq : 0 < q) : 0 < halfWidth q Q := by
  have h1 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have h2 : (0 : ℝ) < (Q : ℝ) + 1 := by positivity
  exact div_pos one_pos (mul_pos h1 h2)

theorem halfWidth_le_of_le {q q' Q : ℕ} (hq' : 0 < q') (h : q' ≤ q) :
    halfWidth q Q ≤ halfWidth q' Q := by
  have h1 : (0 : ℝ) < (q' : ℝ) := by exact_mod_cast hq'
  have h2 : (q' : ℝ) ≤ (q : ℝ) := by exact_mod_cast h
  have h3 : (0 : ℝ) < (Q : ℝ) + 1 := by positivity
  exact one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_right h2 h3.le)

/-- **The design inequality.** `1/(Q+1) + 1/(q(Q+1)) ≤ 1/q` as soon as `q ≤ Q`: the window of
modulus `q` together with the window of modulus `1` still fits strictly inside the gap from `a/q`
to the nearest integer. Everything geometric below is this one inequality. -/
theorem gap_ge {q Q : ℕ} (hq : 0 < q) (hqQ : q ≤ Q) :
    halfWidth 1 Q + halfWidth q Q ≤ 1 / (q : ℝ) := by
  have hqr : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hQr : (0 : ℝ) < (Q : ℝ) + 1 := by positivity
  have hqQr : (q : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hqQ
  have e1 : halfWidth 1 Q = 1 / ((Q : ℝ) + 1) := by unfold halfWidth; norm_num
  have e2 : halfWidth q Q = 1 / ((q : ℝ) * ((Q : ℝ) + 1)) := rfl
  rw [e1, e2, ← sub_nonneg]
  have key : 1 / (q : ℝ) - (1 / ((Q : ℝ) + 1) + 1 / ((q : ℝ) * ((Q : ℝ) + 1)))
      = ((Q : ℝ) - (q : ℝ)) / ((q : ℝ) * ((Q : ℝ) + 1)) := by
    field_simp; ring
  rw [key]
  exact div_nonneg (by linarith) (by positivity)

theorem halfWidth_one_le_half {Q : ℕ} (hQ : 1 ≤ Q) : halfWidth 1 Q ≤ 1 / 2 := by
  have h : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
  have e1 : halfWidth 1 Q = 1 / ((Q : ℝ) + 1) := by unfold halfWidth; norm_num
  rw [e1]
  exact one_div_le_one_div_of_le (by norm_num) (by linarith)

/-! ## The windows sit inside one translated period, and cover it -/

/-- Every window of modulus `q ≥ 2` is strictly inside the period `(-w₁, 1-w₁)`. This is where
`2P < Q+1` is spent the first time. -/
theorem win_subset_Ioc {P Q q a : ℕ} (hsep : 2 * P < Q + 1) (hq1 : 1 ≤ q) (hqP : q ≤ P)
    (ha : a ∈ red q) (hq2 : 2 ≤ q) :
    win q Q a ⊆ Set.Ioc (-halfWidth 1 Q) (1 - halfWidth 1 Q) := by
  rw [mem_red_iff] at ha
  have hqQ : q ≤ Q := by omega
  have ha0 : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with h | h
    · exfalso; rw [h, Nat.gcd_zero_left] at ha; omega
    · exact h
  have hqr : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq1
  have har : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha0
  have haq : (a : ℝ) ≤ (q : ℝ) - 1 := by
    have : (a : ℝ) + 1 ≤ (q : ℝ) := by exact_mod_cast ha.1
    linarith
  have hgap := gap_ge hq1 hqQ
  have hw1 : 0 < halfWidth 1 Q := halfWidth_pos (by norm_num)
  have hlow : 1 / (q : ℝ) ≤ (a : ℝ) / (q : ℝ) := by
    gcongr
  have hhigh : (a : ℝ) / (q : ℝ) ≤ 1 - 1 / (q : ℝ) := by
    rw [div_le_iff₀ hqr]
    have : (1 : ℝ) / (q : ℝ) * (q : ℝ) = 1 := by field_simp
    nlinarith [this]
  intro x hx
  rw [win, Metric.mem_closedBall, Real.dist_eq, abs_le] at hx
  constructor
  · nlinarith [hx.1, hlow, hgap, hw1]
  · nlinarith [hx.2, hhigh, hgap]

/-- The modulus-`1` window is inside the closed period. -/
theorem win_one_subset_Icc {Q : ℕ} (hQ : 1 ≤ Q) :
    win 1 Q 0 ⊆ Set.Icc (-halfWidth 1 Q) (1 - halfWidth 1 Q) := by
  intro x hx
  rw [win, Metric.mem_closedBall, Real.dist_eq, abs_le] at hx
  have hh := halfWidth_one_le_half hQ
  simp only [Nat.cast_zero, Nat.cast_one, zero_div, sub_zero] at hx
  exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

/-- Every reduced window with `q ≤ P` is one of the balls of `MajorArcs P Q`. -/
theorem win_subset_majorArcs {P Q q a : ℕ} (hq1 : 1 ≤ q) (hqP : q ≤ P) :
    win q Q a ⊆ MajorArcs P Q := by
  intro x hx
  rw [win, Metric.mem_closedBall] at hx
  refine Set.mem_biUnion (Set.mem_Icc.mpr ⟨hq1, hqP⟩) ?_
  refine Set.mem_iUnion.mpr ⟨(a : ℤ), ?_⟩
  rw [Metric.mem_closedBall]
  have hcast : ((a : ℤ) : ℝ) / (q : ℝ) = (a : ℝ) / (q : ℝ) := by push_cast; ring
  rw [hcast]
  exact hx

/-- **Reduction to lowest terms, inside one period.** Every point of the major set lying strictly
inside the translated period `(-w₁, 1-w₁)` lies in a *reduced* window `win q Q a` with `q ≤ P` and
`a ∈ red q`. This is where `2P < Q+1` is spent the second time: it forces the numerator into
`[0, q)` before any reduction, so the reduction itself is a bare `Nat.gcd` computation. -/
theorem exists_win_of_mem_majorArcs {P Q : ℕ} (hsep : 2 * P < Q + 1) {x : ℝ}
    (hx : x ∈ MajorArcs P Q) (hlo : -halfWidth 1 Q < x) (hhi : x < 1 - halfWidth 1 Q) :
    ∃ q ∈ Finset.Icc 1 P, ∃ a ∈ red q, x ∈ win q Q a := by
  simp only [MajorArcs, Set.mem_iUnion, Metric.mem_closedBall, Real.dist_eq, exists_prop,
    Set.mem_Icc] at hx
  obtain ⟨q, ⟨hq1, hqP⟩, a, hb⟩ := hx
  have hqr : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq1
  have hwq : halfWidth q Q ≤ halfWidth 1 Q := halfWidth_le_of_le (by norm_num) hq1
  have hw1 : 0 < halfWidth 1 Q := halfWidth_pos (by norm_num)
  have hbq : |x - ((a : ℤ) : ℝ) / (q : ℝ)| ≤ halfWidth q Q := hb
  rw [abs_le] at hbq
  -- `2·w₁ ≤ 1/q`, the separation condition in the form that pins the numerator
  have h2w : 2 * halfWidth 1 Q ≤ 1 / (q : ℝ) := by
    have hQr : (0 : ℝ) < (Q : ℝ) + 1 := by positivity
    have hle : 2 * (q : ℝ) ≤ (Q : ℝ) + 1 := by
      have : 2 * q ≤ Q + 1 := by omega
      exact_mod_cast this
    have e1 : halfWidth 1 Q = 1 / ((Q : ℝ) + 1) := by unfold halfWidth; norm_num
    rw [e1, ← sub_nonneg]
    have key : 1 / (q : ℝ) - 2 * (1 / ((Q : ℝ) + 1))
        = ((Q : ℝ) + 1 - 2 * (q : ℝ)) / ((q : ℝ) * ((Q : ℝ) + 1)) := by field_simp
    rw [key]
    exact div_nonneg (by linarith) (by positivity)
  -- the numerator is already in `[0, q)`
  have hup : ((a : ℤ) : ℝ) / (q : ℝ) < 1 := by linarith
  have hdn : -(1 / (q : ℝ)) < ((a : ℤ) : ℝ) / (q : ℝ) := by linarith
  have haq : a < (q : ℤ) := by
    rw [div_lt_one hqr] at hup
    exact_mod_cast hup
  have ha0 : (0 : ℤ) ≤ a := by
    have hsum : (0 : ℝ) < (((a : ℤ) : ℝ) + 1) / (q : ℝ) := by
      have e : (((a : ℤ) : ℝ) + 1) / (q : ℝ) = ((a : ℤ) : ℝ) / (q : ℝ) + 1 / (q : ℝ) := by ring
      rw [e]; linarith
    have hexp : ((a : ℤ) : ℝ) + 1 = ((((a : ℤ) : ℝ) + 1) / (q : ℝ)) * (q : ℝ) := by field_simp
    have hpos : (0 : ℝ) < ((a : ℤ) : ℝ) + 1 := by rw [hexp]; exact mul_pos hsum hqr
    have : (-1 : ℝ) < ((a : ℤ) : ℝ) := by linarith
    have : (-1 : ℤ) < a := by exact_mod_cast this
    omega
  -- reduce `a/q` by the gcd; everything happens in `ℕ`
  obtain ⟨n, hn⟩ : ∃ n : ℕ, a = (n : ℤ) := ⟨a.toNat, by omega⟩
  have hnq : n < q := by omega
  set g := Nat.gcd n q with hgdef
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_right n hq1
  have hgn : g ∣ n := Nat.gcd_dvd_left n q
  have hgq : g ∣ q := Nat.gcd_dvd_right n q
  refine ⟨q / g, Finset.mem_Icc.mpr ⟨?_, ?_⟩, n / g, ?_, ?_⟩
  · exact Nat.div_pos (Nat.le_of_dvd hq1 hgq) hgpos
  · exact le_trans (Nat.div_le_self q g) hqP
  · refine mem_red_iff.mpr ⟨?_, Nat.coprime_div_gcd_div_gcd hgpos⟩
    have h1 : n / g * g = n := Nat.div_mul_cancel hgn
    have h2 : q / g * g = q := Nat.div_mul_cancel hgq
    exact lt_of_mul_lt_mul_right (by rw [h1, h2]; exact hnq) (Nat.zero_le g)
  · have hgr : (0 : ℝ) < (g : ℝ) := by exact_mod_cast hgpos
    have h1 : ((n / g : ℕ) : ℝ) * (g : ℝ) = (n : ℝ) := by
      rw [← Nat.cast_mul, Nat.div_mul_cancel hgn]
    have h2 : ((q / g : ℕ) : ℝ) * (g : ℝ) = (q : ℝ) := by
      rw [← Nat.cast_mul, Nat.div_mul_cancel hgq]
    have hq'r : (0 : ℝ) < ((q / g : ℕ) : ℝ) := by
      have : 0 < q / g := Nat.div_pos (Nat.le_of_dvd hq1 hgq) hgpos
      exact_mod_cast this
    have heq : ((n / g : ℕ) : ℝ) / ((q / g : ℕ) : ℝ) = ((a : ℤ) : ℝ) / (q : ℝ) := by
      rw [hn, Int.cast_natCast, ← h1, ← h2]
      rw [mul_div_mul_right _ _ (ne_of_gt hgr)]
    have hwle : halfWidth q Q ≤ halfWidth (q / g) Q := by
      refine halfWidth_le_of_le (by exact_mod_cast hq'r) (Nat.div_le_self q g)
    rw [win, Metric.mem_closedBall, Real.dist_eq, heq, abs_le]
    exact ⟨by linarith [hbq.1], by linarith [hbq.2]⟩

/-- **Farey separation.** Distinct reduced fractions with denominators `≤ P` have disjoint windows
once `2P < Q+1`: the anchors are `≥ 1/(qq')` apart while the two windows total
`(q+q')/(qq'(Q+1))` wide. -/
theorem win_disjoint {P Q q q' a a' : ℕ} (hsep : 2 * P < Q + 1)
    (hq1 : 1 ≤ q) (hqP : q ≤ P) (hq1' : 1 ≤ q') (hqP' : q' ≤ P)
    (ha : a ∈ red q) (ha' : a' ∈ red q') (hne : ¬(q = q' ∧ a = a')) :
    Disjoint (win q Q a) (win q' Q a') := by
  rw [Set.disjoint_left]
  intro x hx hx'
  rw [mem_red_iff] at ha ha'
  have hqr : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq1
  have hq'r : (0 : ℝ) < (q' : ℝ) := by exact_mod_cast hq1'
  have hpos : (0 : ℝ) < (q : ℝ) * (q' : ℝ) := mul_pos hqr hq'r
  -- the two anchors are distinct rationals
  have hnum : (a : ℤ) * (q' : ℤ) ≠ (a' : ℤ) * (q : ℤ) := by
    intro h
    refine hne ?_
    have hN : a * q' = a' * q := by exact_mod_cast h
    have hcq : Nat.Coprime q a := Nat.Coprime.symm ha.2
    have hcq' : Nat.Coprime q' a' := Nat.Coprime.symm ha'.2
    have hd1 : q ∣ q' := by
      refine hcq.dvd_of_dvd_mul_left ?_
      exact ⟨a', by rw [hN]; ring⟩
    have hd2 : q' ∣ q := by
      refine hcq'.dvd_of_dvd_mul_left ?_
      exact ⟨a, by rw [← hN]; ring⟩
    have hqq : q = q' := Nat.dvd_antisymm hd1 hd2
    subst hqq
    exact ⟨rfl, Nat.eq_of_mul_eq_mul_right hq1 hN⟩
  -- the anchors are at least `1/(qq')` apart
  set N : ℤ := (a : ℤ) * (q' : ℤ) - (a' : ℤ) * (q : ℤ) with hNdef
  have hN1 : (1 : ℝ) ≤ |(N : ℝ)| := by
    have h1 : (1 : ℤ) ≤ |N| := Int.one_le_abs (sub_ne_zero.mpr hnum)
    have h2 : ((1 : ℤ) : ℝ) ≤ ((|N| : ℤ) : ℝ) := by exact_mod_cast h1
    rwa [Int.cast_abs, Int.cast_one] at h2
  have hval : (a : ℝ) / (q : ℝ) - (a' : ℝ) / (q' : ℝ) = (N : ℝ) / ((q : ℝ) * (q' : ℝ)) := by
    rw [hNdef]; push_cast; field_simp
  have hd : (1 : ℝ) / ((q : ℝ) * (q' : ℝ)) ≤ |(a : ℝ) / (q : ℝ) - (a' : ℝ) / (q' : ℝ)| := by
    rw [hval, abs_div, abs_of_pos hpos, ← sub_nonneg]
    have key : |(N : ℝ)| / ((q : ℝ) * (q' : ℝ)) - 1 / ((q : ℝ) * (q' : ℝ))
        = (|(N : ℝ)| - 1) / ((q : ℝ) * (q' : ℝ)) := by field_simp
    rw [key]
    exact div_nonneg (by linarith) hpos.le
  -- but the two windows together are narrower than that
  have hsum : halfWidth q Q + halfWidth q' Q < 1 / ((q : ℝ) * (q' : ℝ)) := by
    have hQr : (0 : ℝ) < (Q : ℝ) + 1 := by positivity
    have hlt : (q : ℝ) + (q' : ℝ) < (Q : ℝ) + 1 := by
      have : q + q' < Q + 1 := by omega
      exact_mod_cast this
    have e : halfWidth q Q + halfWidth q' Q
        = ((q : ℝ) + (q' : ℝ)) / ((q : ℝ) * (q' : ℝ) * ((Q : ℝ) + 1)) := by
      unfold halfWidth; field_simp; ring
    rw [e, ← sub_pos]
    have key : 1 / ((q : ℝ) * (q' : ℝ))
          - ((q : ℝ) + (q' : ℝ)) / ((q : ℝ) * (q' : ℝ) * ((Q : ℝ) + 1))
        = ((Q : ℝ) + 1 - ((q : ℝ) + (q' : ℝ))) / ((q : ℝ) * (q' : ℝ) * ((Q : ℝ) + 1)) := by
      field_simp
    rw [key]
    exact div_pos (by linarith) (by positivity)
  have htri : |(a : ℝ) / (q : ℝ) - (a' : ℝ) / (q' : ℝ)| ≤ halfWidth q Q + halfWidth q' Q := by
    rw [win, Metric.mem_closedBall, Real.dist_eq, abs_le] at hx hx'
    rw [abs_le]
    exact ⟨by linarith [hx.1, hx'.2], by linarith [hx.2, hx'.1]⟩
  linarith

/-! ## The major set is one period of a periodic integrand -/

/-- `MajorArcs P Q` is invariant under integer translation: the ball about `a/q` goes to the ball
about `(a + kq)/q`. -/
theorem majorArcs_add_intCast {P Q : ℕ} (k : ℤ) {x : ℝ} (hx : x ∈ MajorArcs P Q) :
    x + (k : ℝ) ∈ MajorArcs P Q := by
  simp only [MajorArcs, Set.mem_iUnion, Metric.mem_closedBall, Real.dist_eq, exists_prop,
    Set.mem_Icc] at hx ⊢
  obtain ⟨q, hq, a, hb⟩ := hx
  have hqr : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq.1
  refine ⟨q, hq, a + k * (q : ℤ), ?_⟩
  have hshift : ((a + k * (q : ℤ) : ℤ) : ℝ) / (q : ℝ) = ((a : ℤ) : ℝ) / (q : ℝ) + (k : ℝ) := by
    push_cast; field_simp
  rw [hshift, show x + (k : ℝ) - (((a : ℤ) : ℝ) / (q : ℝ) + (k : ℝ))
    = x - ((a : ℤ) : ℝ) / (q : ℝ) by ring]
  exact hb

/-- The circle-method integrand cut down to the major set is `1`-periodic — `kern_periodic` for the
values, integer translation invariance of `MajorArcs` for the support. -/
theorem kernIndicator_periodic (H P Q : ℕ) :
    Function.Periodic (Set.indicator (MajorArcs P Q) (kern H)) 1 := by
  intro x
  by_cases h : x ∈ MajorArcs P Q
  · have h1 : x + 1 ∈ MajorArcs P Q := by
      simpa using majorArcs_add_intCast (P := P) (Q := Q) 1 h
    rw [Set.indicator_of_mem h1, Set.indicator_of_mem h, kern_periodic]
  · have h1 : x + 1 ∉ MajorArcs P Q := by
      intro hc
      have h2 := majorArcs_add_intCast (P := P) (Q := Q) (-1) hc
      rw [show x + 1 + ((-1 : ℤ) : ℝ) = x by push_cast; ring] at h2
      exact h h2
    rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h]

/-! ## Assembly of Link M1 -/

/-- The union of the reduced windows of one modulus — the set `MajorPlatt.arcSum` integrates
over. -/
noncomputable def arcSet (q Q : ℕ) : Set ℝ := ⋃ a ∈ red q, win q Q a

theorem measurableSet_arcSet (q Q : ℕ) : MeasurableSet (arcSet q Q) :=
  Finset.measurableSet_biUnion _ (fun a _ => measurableSet_win q Q a)

theorem integrableOn_win (H q Q a : ℕ) : IntegrableOn (kern H) (win q Q a) volume := by
  rw [win, Real.closedBall_eq_Icc]
  exact (continuous_kern H).integrableOn_Icc

theorem integrableOn_arcSet (H q Q : ℕ) : IntegrableOn (kern H) (arcSet q Q) volume :=
  integrableOn_finset_iUnion.2 (fun a _ => integrableOn_win H q Q a)

/-- The recentring: `MajorPlatt.windowIntegral` is the integral over the window as a set. -/
theorem windowIntegral_eq (H q Q a : ℕ) (hq : 0 < q) :
    windowIntegral H q Q a = ∫ x in win q Q a, kern H x := by
  have hw : (0 : ℝ) < halfWidth q Q := halfWidth_pos hq
  rw [windowIntegral, win, Real.closedBall_eq_Icc, integral_Icc_eq_integral_Ioc,
    integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -halfWidth q Q ≤ halfWidth q Q),
    ← intervalIntegral.integral_of_le (by linarith :
      (a : ℝ) / (q : ℝ) - halfWidth q Q ≤ (a : ℝ) / (q : ℝ) + halfWidth q Q),
    intervalIntegral.integral_comp_add_left (fun x => kern H x) ((a : ℝ) / (q : ℝ)),
    show (a : ℝ) / (q : ℝ) + -halfWidth q Q = (a : ℝ) / (q : ℝ) - halfWidth q Q from by ring]

theorem integral_arcSet {P Q : ℕ} (hsep : 2 * P < Q + 1) (H q : ℕ) (hq1 : 1 ≤ q) (hqP : q ≤ P) :
    ∫ x in arcSet q Q, kern H x = arcSum H q Q := by
  have hdisj : (↑(red q) : Set ℕ).Pairwise (Function.onFun Disjoint (fun a => win q Q a)) := by
    intro a ha b hb hab
    rw [Finset.mem_coe] at ha hb
    exact win_disjoint hsep hq1 hqP hq1 hqP ha hb (fun h => hab h.2)
  rw [arcSet, integral_biUnion_finset (red q) (fun a _ => measurableSet_win q Q a) hdisj
    (fun a _ => integrableOn_win H q Q a), arcSum]
  exact Finset.sum_congr rfl (fun a _ => (windowIntegral_eq H q Q a hq1).symm)

/-- **LINK M1, DISCHARGED.** At any Farey cutoffs with `1 ≤ P` and `2P < Q+1`, the major-arc
integral is the sum over `q ≤ P` of the per-modulus arc sums.

The proof is three moves and no analysis. (1) `majorIntegral` is the integral of the indicator of
the major set over one period, so `kernIndicator_periodic` lets the period be *shifted* to
`(-w₁, 1-w₁)`, which is the only way the endpoint identification of `(0,1]` can be handled: the
half of the modulus-`1` window sticking out to the left of `0` is the half sticking in at `1`.
(2) Inside that shifted period the major set **is** the union of the reduced windows, up to the two
endpoints `-w₁` and `1-w₁` — `exists_win_of_mem_majorArcs` for `⊆`, `win_subset_majorArcs` plus
`win_subset_Ioc` for `⊇` — and two points are Lebesgue-null. (3) The union is disjoint by
`win_disjoint`, so `integral_biUnion_finset` splits it. -/
theorem majorIntegral_eq_sum_arcSum (H P Q : ℕ) (hP : 1 ≤ P) (hsep : 2 * P < Q + 1) :
    majorIntegral H P Q = ∑ q ∈ Finset.Icc 1 P, arcSum H q Q := by
  have hQ1 : 1 ≤ Q := by omega
  have hw1 : (0 : ℝ) < halfWidth 1 Q := halfWidth_pos (by norm_num)
  have hmA : MeasurableSet (MajorArcs P Q) := MinorArc.measurableSet_majorArcs P Q
  have hper : Function.Periodic (Set.indicator (MajorArcs P Q) (kern H)) 1 :=
    kernIndicator_periodic H P Q
  -- (1) shift the period so that every reduced window lies inside it
  have e1 : majorIntegral H P Q
      = ∫ x in Set.Ioc (0 : ℝ) 1, Set.indicator (MajorArcs P Q) (kern H) x := by
    rw [majorIntegral, majorSet, setIntegral_indicator hmA]
  have e2 : (∫ x in Set.Ioc (0 : ℝ) 1, Set.indicator (MajorArcs P Q) (kern H) x)
      = ∫ x in (0 : ℝ)..(0 + 1), Set.indicator (MajorArcs P Q) (kern H) x := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 0 + 1)]
    norm_num
  have e3 : (∫ x in (0 : ℝ)..(0 + 1), Set.indicator (MajorArcs P Q) (kern H) x)
      = ∫ x in (-halfWidth 1 Q)..(-halfWidth 1 Q + 1),
          Set.indicator (MajorArcs P Q) (kern H) x :=
    hper.intervalIntegral_add_eq 0 (-halfWidth 1 Q)
  have e4 : (∫ x in (-halfWidth 1 Q)..(-halfWidth 1 Q + 1),
        Set.indicator (MajorArcs P Q) (kern H) x)
      = ∫ x in Set.Ioc (-halfWidth 1 Q) (1 - halfWidth 1 Q) ∩ MajorArcs P Q, kern H x := by
    rw [intervalIntegral.integral_of_le (by linarith :
        -halfWidth 1 Q ≤ -halfWidth 1 Q + 1),
      show -halfWidth 1 Q + 1 = 1 - halfWidth 1 Q from by ring, setIntegral_indicator hmA]
  -- (2) inside the shifted period the major set is the union of the reduced windows
  have hae : (Set.Ioc (-halfWidth 1 Q) (1 - halfWidth 1 Q) ∩ MajorArcs P Q : Set ℝ)
      =ᵐ[volume] (⋃ q ∈ Finset.Icc 1 P, arcSet q Q : Set ℝ) := by
    rw [MeasureTheory.ae_eq_set]
    refine ⟨measure_mono_null ?_ (measure_singleton (1 - halfWidth 1 Q)),
      measure_mono_null ?_ (measure_singleton (-halfWidth 1 Q))⟩
    · intro x hx
      obtain ⟨⟨hxI, hxA⟩, hxU⟩ := hx
      rw [Set.mem_singleton_iff]
      by_contra hne
      obtain ⟨q, hq, a, ha, hw⟩ :=
        exists_win_of_mem_majorArcs hsep hxA hxI.1 (lt_of_le_of_ne hxI.2 hne)
      exact hxU (Set.mem_biUnion hq (Set.mem_biUnion ha hw))
    · intro x hx
      obtain ⟨hxU, hxn⟩ := hx
      simp only [Set.mem_iUnion, exists_prop] at hxU
      obtain ⟨q, hq, hxq⟩ := hxU
      rw [Finset.mem_Icc] at hq
      simp only [arcSet, Set.mem_iUnion, exists_prop] at hxq
      obtain ⟨a, ha, hw⟩ := hxq
      have hxA : x ∈ MajorArcs P Q := win_subset_majorArcs hq.1 hq.2 hw
      rcases Nat.lt_or_ge q 2 with h2 | h2
      · have hq1 : q = 1 := by omega
        subst hq1
        have ha0 : a = 0 := by have := (mem_red_iff.mp ha).1; omega
        subst ha0
        have hIcc := win_one_subset_Icc hQ1 hw
        rw [Set.mem_singleton_iff]
        by_contra hne
        exact hxn ⟨⟨lt_of_le_of_ne hIcc.1 (Ne.symm hne), hIcc.2⟩, hxA⟩
      · exact absurd (Set.mem_inter (win_subset_Ioc hsep hq.1 hq.2 ha h2 hw) hxA) hxn
  -- (3) split the disjoint union
  have hdisj : (↑(Finset.Icc 1 P) : Set ℕ).Pairwise
      (Function.onFun Disjoint (fun q => arcSet q Q)) := by
    intro q hq q' hq' hne
    rw [Finset.mem_coe, Finset.mem_Icc] at hq hq'
    rw [Function.onFun, Set.disjoint_left]
    intro x hx hx'
    simp only [arcSet, Set.mem_iUnion, exists_prop] at hx hx'
    obtain ⟨a, ha, hwa⟩ := hx
    obtain ⟨a', ha', hwa'⟩ := hx'
    exact Set.disjoint_left.mp
      (win_disjoint hsep hq.1 hq.2 hq'.1 hq'.2 ha ha' (fun h => hne h.1)) hwa hwa'
  rw [e1, e2, e3, e4, setIntegral_congr_set hae,
    integral_biUnion_finset _ (fun q _ => measurableSet_arcSet q Q) hdisj
      (fun q _ => integrableOn_arcSet H q Q)]
  exact Finset.sum_congr rfl (fun q hq =>
    integral_arcSet hsep H q (Finset.mem_Icc.mp hq).1 (Finset.mem_Icc.mp hq).2)

/-- **`MajorPlatt.FareyDecomposition` is a theorem.** The one slot of
`MajorPlatt.cite_Helfgott_weighted_of_platt_chain` that was pure measure theory. -/
theorem fareyDecomposition_holds : MajorPlatt.FareyDecomposition := fun H hH =>
  majorIntegral_eq_sum_arcSum H (Pcut H) (Qcut H) (by norm_num [Pcut])
    (cutoff_separation H hH)

/-! ## Link M3 — the kernel truncation loss

`KernelTailBound (1/10⁵)` is **TRUE**, and it is not close. The crude chargeable bound is
`∑_{q ≤ P} |T₃(q)|·(q(Q+1))²/8`, and at `H = 10²⁷`

* `∑_{q ≤ 3·10⁵, q squarefree} (q/φ(q))² = 583116.306` (rigorous integer bounds at scale `10⁹`:
  `[583116.30619, 583116.30638]`; the sup-weight `|T₃(q)| ≤ 1/φ(q)²` is used, with
  `max_{q ≤ 3·10⁵} q/φ(q) = 5.2135` at `q = 270270 = 2·3³·5·7·11·13`),
* `(Q+1) = ⌊H/1.2·10⁶⌋ + 1`, so the aggregate loss is `≤ 5.06·10⁻⁸·H²` — **inside `cK = 10⁻⁵` by
  197.6×**. With the true `H`-dependent Ramanujan weight at `H = 10²⁷+1` it is `5.11·10⁻¹¹·H²`,
  inside by `1.96·10⁵`.

*Reconciliation with `MajorFromPlatt` — CORRECTED 2026-09-29, the first version of this paragraph
was wrong twice.* That file's Link-M3 docstring records the loss as `≈ 4.33·10⁵·H²/W²`, and this
paragraph used to say the `6×` gap to the `5.06·10⁻⁸` here was *entirely* the weight change. Both
figures are wrong (round-5 audit, and an independent coordinator recomputation agreeing):

* the coefficient with the LOOSER weight `|T₃(q)| ≤ q/φ(q)³` is
  `(1/8)·∑_{q ≤ 3·10⁵, q squarefree} q³/φ(q)³ = 1.6619·10⁵`, **not** `4.33·10⁵`;
* with the sharper `|T₃(q)| ≤ 1/φ(q)²` (what `|c_q(H)| ≤ φ(q)` actually gives) it is
  `(1/8)·∑ q²/φ(q)² = 7.289·10⁴`;
* so the weight change is worth a factor **2.28**, not 6 — the rest of the apparent gap was the
  wrong coefficient.

The VERDICT is unaffected and that is why this is a nit rather than a defect: the loose weight gives
`1.15·10⁻⁷·H²`, the sharp one `5.06·10⁻⁸·H²`, and `cK = 10⁻⁵` is met with orders to spare either
way. But "the two do not disagree, here is why" was a false reconciliation, and a false
reconciliation
is worse than an unexplained discrepancy: it retires the question.

The chain proved below is deliberately cruder than that so every step is a numeral: it carries the
weight sum at `cL = 10⁶` (against the true `5.83·10⁵`) and the tail constant at `cT = 1/8`, uses
`(Q+1) ≤ H/10⁶` (true from `H ≥ 6·10⁶`) rather than the sharp `H/1.2·10⁶`, and still lands at
`1.25·10⁻⁷·H²`, **inside `10⁻⁵` by 80×**.

**The `Θ(H²)` shape is the right shape** and `MajorFromPlatt`'s docstring is right to insist on it:
`geomTail_sq_scale` proves the chargeable geometric term is `≥ H²/(1.152·10¹³)` — bounded below by a
constant times `H²`, so it can never be charged against `errScale H = H^{3/2}log²H`. The `24.6×`
figure in that docstring is about the `100·errScale` comparison, **not** about `cK·H²`, and the two
must not be conflated: at the `H²` scale the link is comfortable, at the `H^{3/2}` scale it is
unsatisfiable for every constant.

What remains are three named obligations — `FullCircleTriple` (orthogonality), `WindowTailGeom`
(the `|U(β)| ≤ 1/(2‖β‖)` tail) and `LocalTermWeightSum` (a finite arithmetic sum, which needs
`q/φ(q) = O(log log q)` on `q ≤ 3·10⁵` to be provable without enumerating `300000` terms). -/

/-- `U(β)³e(−Hβ)`, the model integrand of `MajorPlatt.kernelIntegral`. -/
noncomputable def modelKernel (H : ℕ) (β : ℝ) : ℂ := (plainSum H β) ^ 3 * e (-(H : ℝ) * β)

theorem kernelIntegral_eq (H q Q : ℕ) :
    kernelIntegral H q Q
      = ∫ β in Set.Icc (-halfWidth q Q) (halfWidth q Q), modelKernel H β := rfl

/-- `(H−1)(H−2)/2 = #{(n₁,n₂,n₃) ∈ [1,H]³ : n₁+n₂+n₃ = H}` — the exact whole-circle value of the
model integrand, and the object `MajorPlatt.KernelTailBound` charges against `H²/2`. -/
noncomputable def tripleCount (H : ℕ) : ℝ := ((H : ℝ) - 1) * ((H : ℝ) - 2) / 2

/-- **Obligation K1 — orthogonality.** `∫₀¹ U(β)³e(−Hβ) dβ` counts ordered triples from `[1,H]`
summing to `H`, so it equals `(H−1)(H−2)/2`. Expand the cube into a triple sum and integrate
`e(kβ)` term by term; `Goldbach.e_eq_one_iff` is the entry point. Exact, not an estimate. -/
def FullCircleTriple : Prop :=
  ∀ H : ℕ, 0 < H → (∫ β in Set.Ioc (0 : ℝ) 1, modelKernel H β) = ((tripleCount H : ℝ) : ℂ)

/-- **Obligation K2 — the geometric truncation tail.** Cutting the period down to
`|β| ≤ w = 1/(q(Q+1))` loses `∫_{w < ‖β‖ ≤ 1/2} U³e(−Hβ)`, and `|U(β)| ≤ 1/(2‖β‖)` gives
`∫_{w<‖β‖≤1/2} 1/(8‖β‖³) = 1/(8w²) − 1/2 = (q(Q+1))²/8 − 1/2`. So `cT = 1/8` is true with the
`−1/2` to spare. The library side is `Goldbach.MinSum.exp_sum_le_sin`. The hypotheses `0 < q`,
`0 < Q` are what make `w ≤ 1/2`, i.e. what stop the "window" being wider than a period. -/
def WindowTailGeom (cT : ℝ) : Prop :=
  ∀ H q Q : ℕ, 0 < q → 0 < Q →
    ‖(∫ β in Set.Ioc (0 : ℝ) 1, modelKernel H β) - kernelIntegral H q Q‖
      ≤ cT * (q : ℝ) ^ 2 * ((Q : ℝ) + 1) ^ 2

/-- **Obligation K3 — the arithmetic weight sum.** `∑_{q ≤ 3·10⁵} |T₃(q)|q² ≤ cL`. Measured
`583116.306` (two ways), so `cL = 10⁶` carries `1.7×`. `|T₃(q)| ≤ 1/φ(q)²` (from
`|c_q(H)| ≤ φ(q)`) reduces it to `∑_{q ≤ P squarefree}(q/φ(q))²`.

**MEASURED 2026-09-29: the totient bound already in this library is NOT enough.**
`SingularSeries.sqfree_totient_strong`'s `μ(q)²/φ(q)² ≤ 8q^{-3/2}` gives only
`|T₃(q)|q² ≤ 8√q`, whose sum is `5.33·10⁸` — which charges `4.63·10⁻⁵·H²` and **exceeds
`cK = 10⁻⁵` by `4.6×`**. The `q^{-3/2}` rate is a `Θ(P^{3/2})` sum where the truth is `Θ(P)`, so
K3 needs the *quality* estimate, not a sharper constant. The route that works, and is the one a
front should be handed: `q²/φ(q)² = ∑_{d ∣ q} h(d)` with `h` multiplicative, `h(p) = (2p−1)/(p−1)²`
and `h(p^a) = 0` for `a ≥ 2`, whence
`∑_{q≤P} q²/φ(q)² = ∑_{d≤P} h(d)⌊P/d⌋ ≤ P·∏_p (1 + h(p)/p) = 4.4311·P`.
At `P = 3·10⁵` that predicts `1329322.7` against the directly summed `1329254.4` — agreeing to
`0.005 %`, which is the check that the identity is the right one. -/
def LocalTermWeightSum (cL : ℝ) : Prop :=
  ∀ H : ℕ, Odd H → 10 ^ 27 ≤ H →
    ∑ q ∈ Finset.Icc 1 (Pcut H), |localTerm q H| * (q : ℝ) ^ 2 ≤ cL

/-! ### The three obligations constrain: no free instance -/

/-- `WindowTailGeom` forces `0 ≤ cT` — it cannot be satisfied by a negative constant, because the
quantity it bounds is a norm. Read at `q = Q = 1`. -/
theorem windowTailGeom_nonneg {cT : ℝ} (h : WindowTailGeom cT) : 0 ≤ cT := by
  have h1 := h 1 1 1 (by norm_num) (by norm_num)
  have h2 : (0 : ℝ) ≤ cT * ((1 : ℕ) : ℝ) ^ 2 * (((1 : ℕ) : ℝ) + 1) ^ 2 :=
    le_trans (norm_nonneg _) h1
  norm_num at h2
  linarith

/-- `LocalTermWeightSum` forces `1 ≤ cL`: the `q = 1` term is `|T₃(1)|·1 = 1` and every term is
`≥ 0`, so no `cL < 1` can satisfy it. -/
theorem localTermWeightSum_one_le {cL : ℝ} (h : LocalTermWeightSum cL) : 1 ≤ cL := by
  have hodd : Odd (10 ^ 27 + 1 : ℕ) := ⟨5 * 10 ^ 26, by norm_num⟩
  have hH : (10 : ℕ) ^ 27 ≤ 10 ^ 27 + 1 := by norm_num
  have h1 := h (10 ^ 27 + 1) hodd hH
  have hmem : (1 : ℕ) ∈ Finset.Icc 1 (Pcut (10 ^ 27 + 1)) := by
    rw [Finset.mem_Icc]; exact ⟨le_rfl, by norm_num [Pcut]⟩
  have hterm : |localTerm 1 (10 ^ 27 + 1)| * ((1 : ℕ) : ℝ) ^ 2 = 1 := by
    simp [localTerm, MajorArcMainTerm.cRam_one]
  have hnn : ∀ q ∈ Finset.Icc 1 (Pcut (10 ^ 27 + 1)),
      0 ≤ |localTerm q (10 ^ 27 + 1)| * (q : ℝ) ^ 2 := fun q _ => by positivity
  have hge := Finset.single_le_sum hnn hmem
  rw [hterm] at hge
  linarith

/-- `MajorPlatt.KernelTailBound` itself forces `0 ≤ cK`, so the slot is not free either. -/
theorem kernelTailBound_nonneg {cK : ℝ} (h : MajorPlatt.KernelTailBound cK) : 0 ≤ cK := by
  have hodd : Odd (10 ^ 27 + 1 : ℕ) := ⟨5 * 10 ^ 26, by norm_num⟩
  have h1 := h (10 ^ 27 + 1) hodd (by norm_num)
  have h2 : (0 : ℝ) ≤ cK * (((10 : ℕ) ^ 27 + 1 : ℕ) : ℝ) ^ 2 :=
    le_trans (Finset.sum_nonneg (fun q _ => norm_nonneg _)) h1
  have h3 : (0 : ℝ) < (((10 : ℕ) ^ 27 + 1 : ℕ) : ℝ) ^ 2 := by positivity
  by_contra hc
  push Not at hc
  nlinarith [h2, h3]

/-- **The offset is real.** `MajorPlatt.KernelTailBound` charges against `H²/2`, but the
whole-circle value is `(H−1)(H−2)/2`; the two differ by exactly `(3H−2)/2`, never zero. So the
`O(H)` term in the composition below is not slack that could be dropped — `FullCircleTriple` could
not have been stated with `H²/2` on the right. -/
theorem tripleCount_sub_sq (H : ℕ) : tripleCount H - (H : ℝ) ^ 2 / 2 = -(3 * (H : ℝ) - 2) / 2 := by
  rw [tripleCount]; ring

theorem tripleCount_ne_sq {H : ℕ} (hH : 0 < H) : tripleCount H ≠ (H : ℝ) ^ 2 / 2 := by
  have hHr : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
  intro hc
  have := tripleCount_sub_sq H
  rw [hc] at this
  simp only [sub_self] at this
  have h2 : (3 : ℝ) * (H : ℝ) - 2 = 0 := by linarith [this]
  linarith

/-! ### The arithmetic of the cutoff -/

theorem qcut_lower (H : ℕ) : (H : ℝ) / 1200000 ≤ (Qcut H : ℝ) + 1 := by
  have h : H < (Qcut H + 1) * 1200000 := by simp only [Qcut]; omega
  have h3 : (H : ℝ) < ((Qcut H : ℝ) + 1) * 1200000 := by
    have h4 : ((H : ℕ) : ℝ) < (((Qcut H + 1) * 1200000 : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at h4
    linarith
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 1200000)]
  linarith

theorem qcut_upper (H : ℕ) (hH : 10 ^ 27 ≤ H) : (Qcut H : ℝ) + 1 ≤ (H : ℝ) / 10 ^ 6 := by
  have hHr : (10 : ℝ) ^ 27 ≤ (H : ℝ) := by exact_mod_cast hH
  have hc : ((Qcut H : ℕ) : ℝ) ≤ (H : ℝ) / 1200000 := by
    have h := (Nat.cast_div_le (α := ℝ) (m := H) (n := 1200000))
    simpa [Qcut] using h
  have key : (H : ℝ) / 10 ^ 6 - ((H : ℝ) / 1200000 + 1) = (H : ℝ) / 6000000 - 1 := by ring
  have hbig : (1 : ℝ) ≤ (H : ℝ) / 6000000 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 6000000)]
    nlinarith [hHr]
  linarith

theorem sq_dominates (H : ℕ) (hH : 10 ^ 27 ≤ H) : (H : ℝ) ≤ (H : ℝ) ^ 2 / 10 ^ 27 := by
  have hHr : (10 : ℝ) ^ 27 ≤ (H : ℝ) := by exact_mod_cast hH
  have h0 : (0 : ℝ) < (H : ℝ) := lt_of_lt_of_le (by norm_num) hHr
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 27)]
  nlinarith [hHr, h0]

/-- **The shape certificate.** The chargeable geometric term at `q = 1` is at least
`H²/(1.152·10¹³)` — a constant times `H²`, for every `H`. So `KernelTailBound`'s `cK·H²` is the
right scale and `errScale H = H^{3/2}log²H` is not: no constant can absorb a `Θ(H²)` loss into an
`H^{3/2}` budget. -/
theorem geomTail_sq_scale (H : ℕ) :
    (H : ℝ) ^ 2 / (1152 * 10 ^ 10) ≤ (1 / 8 : ℝ) * ((Qcut H : ℝ) + 1) ^ 2 := by
  have h1 := qcut_lower H
  have h2 : (0 : ℝ) ≤ (H : ℝ) / 1200000 := by positivity
  nlinarith [h1, h2]

/-! ### The composition -/

/-- **K1 + K2 + K3 ⇒ `MajorPlatt.KernelTailBound cK`**, with the budget as one visible side
condition. Three moves: split `kernelIntegral − H²/2` at the whole-circle value (`FullCircleTriple`
names it, `WindowTailGeom` bounds the distance to it, `tripleCount_sub_sq` is the `O(H)` remainder);
pull the `q`-independent factor out with `q² ≥ 1`; then `LocalTermWeightSum` absorbs the sum and
`qcut_upper` / `sq_dominates` turn both remaining terms into multiples of `H²`. -/
theorem kernelTailBound_of_links {cT cL cK : ℝ} (hcT : 0 ≤ cT) (hcL : 0 ≤ cL)
    (fc : FullCircleTriple) (wt : WindowTailGeom cT) (lw : LocalTermWeightSum cL)
    (hbud : cT * cL / 10 ^ 12 + 3 * cL / (2 * 10 ^ 27) ≤ cK) :
    MajorPlatt.KernelTailBound cK := by
  intro H hodd hH
  have habs : ∀ x : ℝ, ‖(x : ℂ)‖ = |x| := fun x => by simp
  have hH0 : 0 < H := lt_of_lt_of_le (by norm_num) hH
  have hHr : (10 : ℝ) ^ 27 ≤ (H : ℝ) := by exact_mod_cast hH
  have hH0r : (0 : ℝ) < (H : ℝ) := lt_of_lt_of_le (by norm_num) hHr
  have hQ0 : 0 < Qcut H := by
    simp only [Qcut]
    exact Nat.div_pos (le_trans (by norm_num) hH) (by norm_num)
  set F : ℝ := cT * ((Qcut H : ℝ) + 1) ^ 2 + 3 * (H : ℝ) / 2 with hFdef
  have hF : 0 ≤ F := by
    rw [hFdef]; exact add_nonneg (mul_nonneg hcT (sq_nonneg _)) (by positivity)
  have hterm : ∀ q ∈ Finset.Icc 1 (Pcut H),
      ‖((localTerm q H : ℝ) : ℂ) * (kernelIntegral H q (Qcut H) - (((H : ℝ) ^ 2 / 2 : ℝ) : ℂ))‖
        ≤ (|localTerm q H| * (q : ℝ) ^ 2) * F := by
    intro q hq
    rw [Finset.mem_Icc] at hq
    have hqr : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq.1
    have hq2 : (1 : ℝ) ≤ (q : ℝ) ^ 2 := by nlinarith
    have hA : ‖kernelIntegral H q (Qcut H) - ((tripleCount H : ℝ) : ℂ)‖
        ≤ cT * (q : ℝ) ^ 2 * ((Qcut H : ℝ) + 1) ^ 2 := by
      have h1 := wt H q (Qcut H) hq.1 hQ0
      rw [fc H hH0, norm_sub_rev] at h1
      exact h1
    have hB : ‖((tripleCount H : ℝ) : ℂ) - (((H : ℝ) ^ 2 / 2 : ℝ) : ℂ)‖ ≤ 3 * (H : ℝ) / 2 := by
      have hn : ((tripleCount H : ℝ) : ℂ) - (((H : ℝ) ^ 2 / 2 : ℝ) : ℂ)
          = ((tripleCount H - (H : ℝ) ^ 2 / 2 : ℝ) : ℂ) := by push_cast; ring
      rw [hn, habs, tripleCount_sub_sq, abs_le]
      constructor <;> linarith
    have hsplit : kernelIntegral H q (Qcut H) - (((H : ℝ) ^ 2 / 2 : ℝ) : ℂ)
        = (kernelIntegral H q (Qcut H) - ((tripleCount H : ℝ) : ℂ))
          + (((tripleCount H : ℝ) : ℂ) - (((H : ℝ) ^ 2 / 2 : ℝ) : ℂ)) := by ring
    have hnorm : ‖kernelIntegral H q (Qcut H) - (((H : ℝ) ^ 2 / 2 : ℝ) : ℂ)‖
        ≤ cT * (q : ℝ) ^ 2 * ((Qcut H : ℝ) + 1) ^ 2 + 3 * (H : ℝ) / 2 := by
      rw [hsplit]
      exact le_trans (norm_add_le _ _) (add_le_add hA hB)
    have hexp : (q : ℝ) ^ 2 * F
        = cT * (q : ℝ) ^ 2 * ((Qcut H : ℝ) + 1) ^ 2 + (q : ℝ) ^ 2 * (3 * (H : ℝ) / 2) := by
      rw [hFdef]; ring
    have hq3 : 3 * (H : ℝ) / 2 ≤ (q : ℝ) ^ 2 * (3 * (H : ℝ) / 2) := by nlinarith [hH0r]
    have hstep : ‖kernelIntegral H q (Qcut H) - (((H : ℝ) ^ 2 / 2 : ℝ) : ℂ)‖ ≤ (q : ℝ) ^ 2 * F := by
      rw [hexp]; linarith
    rw [norm_mul, habs]
    calc |localTerm q H| * ‖kernelIntegral H q (Qcut H) - (((H : ℝ) ^ 2 / 2 : ℝ) : ℂ)‖
        ≤ |localTerm q H| * ((q : ℝ) ^ 2 * F) :=
          mul_le_mul_of_nonneg_left hstep (abs_nonneg _)
      _ = (|localTerm q H| * (q : ℝ) ^ 2) * F := by ring
  have hsum1 := Finset.sum_le_sum hterm
  rw [← Finset.sum_mul] at hsum1
  have hchain : (∑ q ∈ Finset.Icc 1 (Pcut H),
      ‖((localTerm q H : ℝ) : ℂ) * (kernelIntegral H q (Qcut H) - (((H : ℝ) ^ 2 / 2 : ℝ) : ℂ))‖)
      ≤ cL * F := by
    refine le_trans hsum1 ?_
    exact mul_le_mul_of_nonneg_right (lw H hodd hH) hF
  refine le_trans hchain ?_
  have hQu : ((Qcut H : ℝ) + 1) ^ 2 ≤ (H : ℝ) ^ 2 / 10 ^ 12 := by
    have h1 := qcut_upper H hH
    have h2 : (0 : ℝ) ≤ (Qcut H : ℝ) + 1 := by positivity
    nlinarith [h1, h2]
  have hHu : (H : ℝ) ≤ (H : ℝ) ^ 2 / 10 ^ 27 := sq_dominates H hH
  have hFle : F ≤ cT * ((H : ℝ) ^ 2 / 10 ^ 12) + 3 * ((H : ℝ) ^ 2 / 10 ^ 27) / 2 := by
    rw [hFdef]
    have := mul_le_mul_of_nonneg_left hQu hcT
    linarith
  have hstep2 : cL * F ≤ cL * (cT * ((H : ℝ) ^ 2 / 10 ^ 12) + 3 * ((H : ℝ) ^ 2 / 10 ^ 27) / 2) :=
    mul_le_mul_of_nonneg_left hFle hcL
  refine le_trans hstep2 ?_
  have heq : cL * (cT * ((H : ℝ) ^ 2 / 10 ^ 12) + 3 * ((H : ℝ) ^ 2 / 10 ^ 27) / 2)
      = (cT * cL / 10 ^ 12 + 3 * cL / (2 * 10 ^ 27)) * (H : ℝ) ^ 2 := by ring
  rw [heq]
  exact mul_le_mul_of_nonneg_right hbud (sq_nonneg _)

/-- **The instantiation the chain wants**, at the constants the numbers support: `cT = 1/8` (true
with `1/2` absolute to spare) and `cL = 10⁶` (measured `5.83·10⁵`). The proved total is
`1.25·10⁻⁷·H²`, inside `cK = 10⁻⁵` by `80×`. -/
theorem kernelTailBound_std (fc : FullCircleTriple) (wt : WindowTailGeom (1 / 8))
    (lw : LocalTermWeightSum (10 ^ 6)) : MajorPlatt.KernelTailBound (1 / 10 ^ 5) :=
  kernelTailBound_of_links (by norm_num) (by norm_num) fc wt lw (by norm_num)

/-- **The chain, with the two slots this file owns removed.** `FareyDecomposition` is gone
(`fareyDecomposition_holds`) and `KernelTailBound (1/10⁵)` is replaced by the three obligations of
Link M3. Of the four hypotheses that remain here, `ss`, `cm` and `pp` are already theorems in
sibling modules — `SingularBridge.singularSeriesLower_holds`,
`CircleMethod.circleMethodIdentity_holds` and `PrimePower.primePowerRemoval_ten` — so what is
genuinely open is `grh` (Platt's computation, never a Lean theorem), `wa` (the analytic heart),
`mn` (the minor-arc sup) and K1–K3. -/
theorem cite_Helfgott_weighted_of_kernel_links (grh : PlattGRH)
    (wa : MajorPlatt.WindowApproxUnder 1000 (1 / 2) (fun q => 10 ^ 8 / (q : ℝ)))
    (fc : FullCircleTriple) (wt : WindowTailGeom (1 / 8))
    (lw : LocalTermWeightSum (10 ^ 6))
    (ss : MajorPlatt.SingularSeriesLower (5 / 4)) (cm : CircleMethodIdentity)
    (mn : MinorSupBound Pcut Qcut (3 / 10)) (pp : PrimePowerRemoval 10) :
    Principia.Erdos1054.Cite_Helfgott_weighted :=
  MajorPlatt.cite_Helfgott_weighted_of_platt_chain grh fareyDecomposition_holds wa
    (kernelTailBound_std fc wt lw) ss cm mn pp

end Principia.Common.TernaryGoldbach.FareyKernel
