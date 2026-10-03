/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.Goldbach.ArcTail

/-!
# Almost-all binary Goldbach, `Harc`: the major-arc L^2 error `harc_proven`

Ported **verbatim** from the circle-method half of the comparator-certified master
`GoldbachChainMaster.lean` (PNT+ workspace, lines 29814–31115; there
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
set_option maxHeartbeats 1000000
open Finset
open MinSum
open Finset
open MinorArc
open scoped ArithmeticFunction
open scoped ArithmeticFunction
open Finset
open MajorArcMainTerm
open Finset

-- ==== harc-chain shims (v3) ====

/-- `bessel_Ioc` discharge: the integrable-`f` Bessel proven in HarcArcTailBound. -/
theorem bessel_Ioc (f : ℝ → ℂ)
    (hf : MeasureTheory.IntegrableOn (fun α => ‖f α‖ ^ 2) (Set.Ioc (0:ℝ) 1)) (M : ℕ) :
    ∑ n ∈ Finset.range M, ‖∫ α in Set.Ioc (0:ℝ) 1, f α * e (-((n : ℝ) * α))‖ ^ 2
      ≤ ∫ α in Set.Ioc (0:ℝ) 1, ‖f α‖ ^ 2 := bessel_Ioc_proven f hf M

/-- `arcs_disjoint` discharge from the pairwise `farey_disjoint`. -/
theorem arcs_disjoint (P Q : ℕ) (hPQ : 2 * P ^ 2 < Q + 1) :
    ((anchors P : Finset (ℕ × ℤ)) : Set (ℕ × ℤ)).Pairwise (Function.onFun Disjoint (arc Q)) := by
  intro pq hpq pq' hpq' hne
  have hmem := Finset.mem_filter.mp (Finset.mem_coe.mp hpq)
  have hmem' := Finset.mem_filter.mp (Finset.mem_coe.mp hpq')
  have hq := (Finset.mem_Icc.mp (Finset.mem_product.mp hmem.1).1)
  have hq' := (Finset.mem_Icc.mp (Finset.mem_product.mp hmem'.1).1)
  have hball := farey_disjoint P Q hPQ pq.2 pq'.2 pq.1 pq'.1
    (by omega) (by omega) hq.2 hq'.2 hmem.2 hmem'.2
    (by
      intro ⟨ha, hqeq⟩
      exact hne (Prod.ext hqeq ha))
  exact Disjoint.mono Set.inter_subset_left Set.inter_subset_left hball

/-!
# harc ARC-TAIL half (major-arc model evaluation → singular-series × kernel)

The second (deepest) half of `harc`, split out to check fast. The arc-tail sub-error is
`l2_error_triangle`'s input `h1 = f − g` with `f = Re coeffModel`, `g = 𝔖_P·r_N`:
`∑_{n∈(X/2,X]}(Re coeffModel − 𝔖_P·r_N)² ≤ εX³`. It evaluates the anchor-window model integral.

Route: per anchor, factor `∑_r e(ra/q)λ = μ(q)/φ(q)` out (`anchor_integrand_eq`), leaving the pure
Dirichlet-kernel arc integral `∫_arc D_N(α−a/q)²e(-nα)`; change variables `β = α−a/q`, giving
`e(-na/q)·(∫_full D_N²e(-nβ) − arc-tail)` = `e(-na/q)·(r_N(n) − ρ_q(n))` [`dirichlet_full`]; sum over
`a` gives the Ramanujan sum `∑_a e(-na/q) = c_q(n)`, so `coeffModel = 𝔖_P·r_N − ∑_q(μ/φ)²∑_a e(-na/q)ρ_q`;
the error `∑_n(⋯ρ_q)² ≤ εX³` via `∫|D_N|⁴` Bessel + Farey almost-orthogonality.

`e`, `lambdaModel`, `anchors`, `coeffModel` are the identical top-level definitions from
`RatedWindow.lean`; `lambdaModel_coeff` / `dirichlet_full` enter as labeled cross-file inputs
(PROVEN in `MinorArcExpSum.lean` / `MajorArcMainTerm.lean`), discharged at Phase-F concatenation.
-/

open MeasureTheory





section Inputs


end Inputs

/-- **Anchor integrand simplification** (arc-tail entry): the singular-series coefficient
    `∑_r e(ra/q)λ = μ(q)/φ(q)` factors out of the anchor integral. -/
lemma anchor_integrand_eq (N n q : ℕ) (a : ℤ) (s : Set ℝ) (hq : 0 < q) (ha : Int.gcd a q = 1) :
    (∫ α in s, ((∑ r ∈ Finset.range q, e ((r : ℝ) * (a : ℝ) / (q : ℝ)) * lambdaModel q r)
        * ∑ k ∈ Finset.range N, e ((k : ℝ) * (α - (a : ℝ) / (q : ℝ)))) ^ 2 * e (-((n : ℝ) * α)))
      = ((ArithmeticFunction.moebius q : ℂ) / (Nat.totient q : ℂ)) ^ 2
        * ∫ α in s, (∑ k ∈ Finset.range N, e ((k : ℝ) * (α - (a : ℝ) / (q : ℝ)))) ^ 2
            * e (-((n : ℝ) * α)) := by
  rw [lambdaModel_coeff a q hq ha, ← integral_const_mul]
  congr 1
  funext α
  ring

/-- **coeffModel factored form**: `coeffModel N P Q n = ∑_{pq∈anchors} (μ(q)/φ(q))²·∫_arc D_N(α−a/q)²·
    e(-nα)`. Pulls the μ/φ singular-series coefficient out of every anchor integral (via
    `anchor_integrand_eq`, `gcd(a,q)=1` and `q ≥ 1` from `anchors` membership). The starting point for
    the arc-integral evaluation `∫_arc D_N² e = e(-na/q)(r_N − ρ_q)`. -/
lemma coeffModel_eq (N P Q n : ℕ) :
    coeffModel N P Q n = ∑ pq ∈ anchors P,
      ((ArithmeticFunction.moebius pq.1 : ℂ) / (Nat.totient pq.1 : ℂ)) ^ 2
        * ∫ α in Metric.closedBall ((pq.2 : ℝ) / (pq.1 : ℕ)) (1 / (pq.1 * (Q + 1)))
            ∩ Set.Ioc (0:ℝ) 1,
          (∑ k ∈ Finset.range N, e ((k : ℝ) * (α - (pq.2 : ℝ) / (pq.1 : ℝ)))) ^ 2
            * e (-((n : ℝ) * α)) := by
  rw [coeffModel]
  apply Finset.sum_congr rfl
  intro pq hpq
  rw [anchors, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hpq
  have hq : 0 < pq.1 := by omega
  have ha : Int.gcd pq.2 pq.1 = 1 := hpq.2
  exact anchor_integrand_eq N n pq.1 pq.2 _ hq ha


/-- **Arc-integral change of variables** `β = α − c` (`c = a/q`): translation-invariance of the arc
    integral, `∫_s D_N(α−c)²e(-nα) = e(-nc)·∫_{s−c} D_N(β)²e(-nβ)`. Shifts each anchor arc to be
    centred at 0, exposing the full-period Dirichlet kernel (`dirichlet_full`). Via `integral_indicator`
    + `integral_add_right_eq_self` (Lebesgue translation-invariance) + `e_add` pulling `e(-nc)` out. -/
lemma arc_change_of_var (N n : ℕ) (c : ℝ) (s : Set ℝ) (hs : MeasurableSet s) :
    (∫ α in s, (∑ k ∈ Finset.range N, e ((k : ℝ) * (α - c))) ^ 2 * e (-((n : ℝ) * α)))
      = e (-((n : ℝ) * c))
        * ∫ β in {β : ℝ | β + c ∈ s}, (∑ k ∈ Finset.range N, e ((k : ℝ) * β)) ^ 2 * e (-((n : ℝ) * β)) := by
  set g := fun α : ℝ => (∑ k ∈ Finset.range N, e ((k : ℝ) * (α - c))) ^ 2 * e (-((n : ℝ) * α)) with hg
  have hs' : MeasurableSet {β : ℝ | β + c ∈ s} := hs.preimage (by fun_prop)
  rw [← integral_indicator hs, ← integral_add_right_eq_self (fun α => Set.indicator s g α) c]
  have hpt : (fun β => Set.indicator s g (β + c))
      = fun β => Set.indicator {β : ℝ | β + c ∈ s} (fun β => g (β + c)) β := by
    funext β
    classical
    rw [Set.indicator_apply, Set.indicator_apply]
    exact if_congr Iff.rfl rfl rfl
  rw [hpt, integral_indicator hs', ← integral_const_mul]
  apply setIntegral_congr_fun hs'
  intro β _
  simp only [hg]
  rw [show (β + c - c) = β by ring,
    show -((n : ℝ) * (β + c)) = -((n : ℝ) * β) + -((n : ℝ) * c) by ring, ← e_add]
  ring


/-- `e(k(β+1)) = e(kβ)` for `k : ℕ` — the additive character is 1-periodic. -/
lemma e_shift_one (k : ℕ) (β : ℝ) : e ((k : ℝ) * (β + 1)) = e ((k : ℝ) * β) := by
  rw [show (k : ℝ) * (β + 1) = (k : ℝ) * β + (k : ℝ) by ring, ← e_add, e_natCast_eq_one, mul_one]

/-- `e(-(n:ℝ)) = 1` for `n : ℕ`. -/
lemma e_neg_natCast_eq_one (n : ℕ) : e (-(n : ℝ)) = 1 := by
  have h2 := e_add (-(n : ℝ)) (n : ℝ)
  rw [e_natCast_eq_one, mul_one, show (-(n : ℝ)) + (n : ℝ) = 0 by ring,
    show e (0 : ℝ) = 1 by simp [e]] at h2
  exact h2

/-- **Integrand 1-periodicity**: `D_N(β+1)²·e(-n(β+1)) = D_N(β)²·e(-nβ)`. The arc integral near `0`
    (after `arc_change_of_var`) relates to the full-period `∫₀¹` (`dirichlet_full`); the arc-tail is
    the complement within one period. -/
lemma arc_integrand_periodic (N n : ℕ) (β : ℝ) :
    (∑ k ∈ Finset.range N, e ((k : ℝ) * (β + 1))) ^ 2 * e (-((n : ℝ) * (β + 1)))
      = (∑ k ∈ Finset.range N, e ((k : ℝ) * β)) ^ 2 * e (-((n : ℝ) * β)) := by
  have hD : (∑ k ∈ Finset.range N, e ((k : ℝ) * (β + 1)))
      = ∑ k ∈ Finset.range N, e ((k : ℝ) * β) :=
    Finset.sum_congr rfl (fun k _ => e_shift_one k β)
  have he : e (-((n : ℝ) * (β + 1))) = e (-((n : ℝ) * β)) := by
    rw [show -((n : ℝ) * (β + 1)) = -((n : ℝ) * β) + -(n : ℝ) by ring, ← e_add,
      e_neg_natCast_eq_one, mul_one]
  rw [hD, he]

/-- **Arc = full − tail**: for a measurable arc `A ⊆ B` (`B = Ioc(0,1)`, the full period) and an
    integrable integrand, `∫_A F = ∫_B F − ∫_{B∖A} F`. The arc integral is the full-period value
    (`dirichlet_full`, `= e(-nc)·r_N`) minus the arc-tail `ρ_q = ∫_{B∖A} F` (whose L² is bounded by the
    Dirichlet `∫|D_N|⁴` on the complement). Via `setIntegral_union` on `B = A ∪ (B∖A)`. -/
lemma arc_split (F : ℝ → ℂ) (A B : Set ℝ) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAB : A ⊆ B) (hint : IntegrableOn F B) :
    (∫ α in A, F α) = (∫ α in B, F α) - ∫ α in B \ A, F α := by
  have hunion : B = A ∪ (B \ A) := (Set.union_diff_cancel hAB).symm
  have hkey : (∫ α in B, F α) = (∫ α in A, F α) + ∫ α in B \ A, F α := by
    conv_lhs => rw [hunion]
    exact setIntegral_union Set.disjoint_sdiff_right (hB.diff hA)
      (hint.mono_set hAB) (hint.mono_set Set.diff_subset)
  rw [hkey]; ring


/-- **Full-period arc value**: `∫_{Ioc(0,1)} D_N(α−c)²e(-nα) = e(-nc)·r_N(n)`. Change of variables
    (`arc_change_of_var`) + periodicity (`∫` over any length-1 interval `= ∫₀¹`, via
    `Function.Periodic.intervalIntegral_add_eq`) + `dirichlet_full`. Combined with `arc_split`, the
    anchor integral is `e(-nc)·r_N − ρ_q(n)`. -/
lemma full_arc_eq (N n : ℕ) (c : ℝ) :
    (∫ α in Set.Ioc (0:ℝ) 1, (∑ k ∈ Finset.range N, e ((k : ℝ) * (α - c))) ^ 2 * e (-((n : ℝ) * α)))
      = e (-((n : ℝ) * c))
        * (((Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 = n)).card : ℂ) := by
  rw [arc_change_of_var N n c (Set.Ioc 0 1) measurableSet_Ioc]
  congr 1
  have hs'eq : {β : ℝ | β + c ∈ Set.Ioc (0:ℝ) 1} = Set.Ioc (-c) (1 - c) := by
    ext β; simp only [Set.mem_setOf_eq, Set.mem_Ioc]; constructor <;> intro h <;>
      exact ⟨by linarith [h.1], by linarith [h.2]⟩
  rw [hs'eq, ← intervalIntegral.integral_of_le (by linarith : (-c) ≤ 1 - c)]
  have hper : Function.Periodic
      (fun β => (∑ k ∈ Finset.range N, e ((k : ℝ) * β)) ^ 2 * e (-((n : ℝ) * β))) 1 :=
    fun β => arc_integrand_periodic N n β
  rw [show (1:ℝ) - c = -c + 1 by ring, hper.intervalIntegral_add_eq (-c) 0, zero_add]
  have := dirichlet_full N n
  simp only [neg_mul] at this ⊢
  exact this

/-- **Per-anchor arc value**: `∫_A D_N(α−c)²e(-nα) = e(-nc)·r_N(n) − ρ_q(n)` for an arc `A ⊆ Ioc(0,1)`,
    where `ρ_q(n) = ∫_{Ioc(0,1)∖A} D_N(α−c)²e(-nα)` is the arc-tail. Combines `arc_split` + `full_arc_eq`
    (integrand continuous ⇒ integrable on the bounded `Ioc`). The clean form fed to `coeffModel_eq`:
    `coeffModel = ∑_pq(μ/φ)²(e(-na/q)·r_N − ρ_q) = 𝔖_P·r_N − E` after the Ramanujan-sum step. -/
lemma anchor_arc_eq (N n : ℕ) (c : ℝ) (A : Set ℝ) (hA : MeasurableSet A)
    (hAsub : A ⊆ Set.Ioc (0:ℝ) 1) :
    (∫ α in A, (∑ k ∈ Finset.range N, e ((k : ℝ) * (α - c))) ^ 2 * e (-((n : ℝ) * α)))
      = e (-((n : ℝ) * c))
          * (((Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 = n)).card : ℂ)
        - ∫ α in Set.Ioc (0:ℝ) 1 \ A,
            (∑ k ∈ Finset.range N, e ((k : ℝ) * (α - c))) ^ 2 * e (-((n : ℝ) * α)) := by
  have hint : IntegrableOn
      (fun α => (∑ k ∈ Finset.range N, e ((k : ℝ) * (α - c))) ^ 2 * e (-((n : ℝ) * α)))
      (Set.Ioc (0:ℝ) 1) := by
    apply Continuous.integrableOn_Ioc
    simp only [e]; fun_prop
  rw [arc_split _ A (Set.Ioc 0 1) hA measurableSet_Ioc hAsub hint, full_arc_eq]


/-- **Arc-tail Bessel**: `∑_{n<M} ‖ρ_q(n)‖² ≤ ∫_{Ioc(0,1)∖A} |D_N(α−c)|⁴`, where
    `ρ_q(n) = ∫_{Ioc(0,1)∖A} D_N(α−c)²e(-nα)` (the arc-tail, `anchor_arc_eq`). Direct `bessel_minor`
    with `f = D_N(·−c)²`. The Dirichlet-L⁴ tail `∫_{|β|>δ_q}|D_N|⁴ ≲ (q(Q+1))³` then bounds it; summing
    over the DISJOINT Farey arcs (`farey_disjoint`) gives the harc arc-tail L² error `∑(Re E)² ≤ εX³`. -/
lemma rho_bessel (N : ℕ) (c : ℝ) (A : Set ℝ) (hA : MeasurableSet A) (M : ℕ) :
    ∑ n ∈ Finset.range M,
        ‖∫ α in Set.Ioc (0:ℝ) 1 \ A,
            (∑ k ∈ Finset.range N, e ((k : ℝ) * (α - c))) ^ 2 * e (-((n : ℝ) * α))‖ ^ 2
      ≤ ∫ α in Set.Ioc (0:ℝ) 1 \ A,
          ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * (α - c))) ^ 2‖ ^ 2 := by
  apply bessel_minor (fun α => (∑ k ∈ Finset.range N, e ((k : ℝ) * (α - c))) ^ 2) ?_
    (Set.Ioc (0:ℝ) 1 \ A) (measurableSet_Ioc.diff hA) Set.diff_subset M
  simp only [e]
  fun_prop



/-- **Disjoint arcs → single integral**: `∑_{i∈s} ∫_{A i} g i = ∫_{⋃_{i∈s} A i} ∑_{i∈s} 1_{A i}·(g i)`
    for pairwise-disjoint measurable `A i`. Expresses the anchor-sum `coeffModel` (via `coeffModel_eq`)
    as ONE integral over the disjoint (`farey_disjoint`) major-arc union — the single-Bessel
    reformulation: the L² error `∑_n|coeffModel − 𝔖_P·r_N|²` becomes ONE `bessel_minor` on `⋃arcs`,
    with the L⁴ tail integrated once (dodging the divergent per-arc/overlapping-complement route). -/
lemma sum_setIntegral_disjoint {ι : Type*} (s : Finset ι) (A : ι → Set ℝ) (g : ι → ℝ → ℂ)
    (hmeas : ∀ i ∈ s, MeasurableSet (A i))
    (hdisj : (s : Set ι).Pairwise (Function.onFun Disjoint A))
    (hint : ∀ i ∈ s, IntegrableOn (g i) (A i)) :
    ∑ i ∈ s, ∫ α in A i, g i α
      = ∫ α in ⋃ i ∈ s, A i, ∑ i ∈ s, (A i).indicator (g i) α := by
  have hpt : ∀ i ∈ s, ∀ α ∈ A i, (∑ j ∈ s, (A j).indicator (g j) α) = g i α := by
    intro i hi α hα
    rw [Finset.sum_eq_single i]
    · rw [Set.indicator_of_mem hα]
    · intro j hj hji
      rw [Set.indicator_of_notMem]
      intro hαj
      exact Set.disjoint_left.mp (hdisj hj hi hji) hαj hα
    · intro hi'; exact absurd hi hi'
  rw [integral_biUnion_finset s hmeas hdisj ?_]
  · apply Finset.sum_congr rfl
    intro i hi
    exact (setIntegral_congr_fun (hmeas i hi) (fun α hα => hpt i hi α hα)).symm
  · intro i hi
    exact (hint i hi).congr_fun (fun α hα => (hpt i hi α hα).symm) (hmeas i hi)



/-- **coeffModel as a single integral** over the disjoint major-arc union `⋃arc` (the single-Bessel
    reformulation): `coeffModel N P Q n = ∫_{⋃arc} ∑_pq 1_{arc}·(μ/φ)²D_N(α−a/q)²·e(-nα)`. From
    `coeffModel_eq` (move `(μ/φ)²` inside via `integral_const_mul`) + `sum_setIntegral_disjoint`
    (`arcs_disjoint`). The L² error is now ONE `bessel_minor` on `⋃arc`. -/
lemma coeffModel_as_integral (N P Q n : ℕ) (hPQ : 2 * P ^ 2 < Q + 1) :
    coeffModel N P Q n
      = ∫ α in ⋃ pq ∈ anchors P, arc Q pq,
        ∑ pq ∈ anchors P, (arc Q pq).indicator
          (fun α => ((ArithmeticFunction.moebius pq.1 : ℂ) / (Nat.totient pq.1 : ℂ)) ^ 2
            * (∑ k ∈ Finset.range N, e ((k : ℝ) * (α - (pq.2 : ℝ) / (pq.1 : ℝ)))) ^ 2
            * e (-((n : ℝ) * α))) α := by
  rw [coeffModel_eq]
  have hmove : ∀ pq ∈ anchors P,
      ((ArithmeticFunction.moebius pq.1 : ℂ) / (Nat.totient pq.1 : ℂ)) ^ 2
        * ∫ α in Metric.closedBall ((pq.2 : ℝ) / (pq.1 : ℕ)) (1 / (pq.1 * (Q + 1)))
            ∩ Set.Ioc (0:ℝ) 1,
          (∑ k ∈ Finset.range N, e ((k : ℝ) * (α - (pq.2 : ℝ) / (pq.1 : ℝ)))) ^ 2 * e (-((n : ℝ) * α))
      = ∫ α in Metric.closedBall ((pq.2 : ℝ) / (pq.1 : ℕ)) (1 / (pq.1 * (Q + 1)))
            ∩ Set.Ioc (0:ℝ) 1,
          ((ArithmeticFunction.moebius pq.1 : ℂ) / (Nat.totient pq.1 : ℂ)) ^ 2
            * (∑ k ∈ Finset.range N, e ((k : ℝ) * (α - (pq.2 : ℝ) / (pq.1 : ℝ)))) ^ 2
            * e (-((n : ℝ) * α)) := by
    intro pq _
    rw [← integral_const_mul]
    apply setIntegral_congr_fun ?_ (fun α _ => by ring)
    exact (Metric.isClosed_closedBall.measurableSet).inter measurableSet_Ioc
  rw [Finset.sum_congr rfl hmove]
  refine sum_setIntegral_disjoint (anchors P) (arc Q) _ ?_ (arcs_disjoint P Q hPQ) ?_
  · intro pq _; exact (Metric.isClosed_closedBall.measurableSet).inter measurableSet_Ioc
  · intro pq _
    have hcont : Continuous (fun α : ℝ =>
        ((ArithmeticFunction.moebius pq.1 : ℂ) / (Nat.totient pq.1 : ℂ)) ^ 2
          * (∑ k ∈ Finset.range N, e ((k : ℝ) * (α - (pq.2 : ℝ) / (pq.1 : ℝ)))) ^ 2
          * e (-((n : ℝ) * α))) := by
      simp only [e]; fun_prop
    exact (hcont.integrableOn_Ioc (a := (0:ℝ)) (b := 1)).mono_set Set.inter_subset_right

/-- The arc-tail integral `ρ_q(n) = ∫_{Ioc(0,1)∖arc} D_N(α−a/q)²·e(-nα)` at anchor `pq=(q,a)`. -/
noncomputable def rhoTail (N Q n : ℕ) (pq : ℕ × ℤ) : ℂ :=
  ∫ α in Set.Ioc (0:ℝ) 1 \ arc Q pq,
    (∑ k ∈ Finset.range N, e ((k : ℝ) * (α - (pq.2 : ℝ) / (pq.1 : ℝ)))) ^ 2 * e (-((n : ℝ) * α))

/-- `coeffModel_eq` restated with the arc integrals folded into `arc Q pq` (defeq, via `rfl`). -/
lemma coeffModel_eq_arc (N P Q n : ℕ) :
    coeffModel N P Q n = ∑ pq ∈ anchors P,
      ((ArithmeticFunction.moebius pq.1 : ℂ) / (Nat.totient pq.1 : ℂ)) ^ 2
        * ∫ α in arc Q pq,
          (∑ k ∈ Finset.range N, e ((k : ℝ) * (α - (pq.2 : ℝ) / (pq.1 : ℝ)))) ^ 2 * e (-((n : ℝ) * α)) := by
  rw [coeffModel_eq]; rfl

/-- **coeffModel = main − error** (the arc-tail split): `coeffModel(n) = r_N·A(n) − E(n)`, where
    `r_N = #{(k,k'): k+k'=n}` (kernel count), `A(n) = ∑_pq (μ/φ)²·e(-na/q)` (Ramanujan main term,
    reconciled to `𝔖_P·` by `ramanujan_main`), and `E(n) = ∑_pq (μ/φ)²·ρ_q(n)` (the arc-tail error,
    bounded by the per-q `rho_bessel` + ℓ² Minkowski route). From `∑_pq (μ/φ)²·anchor_arc_eq`. -/
lemma coeffModel_main_minus_error (N P Q n : ℕ) :
    coeffModel N P Q n
      = (((Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 = n)).card : ℂ)
          * (∑ pq ∈ anchors P,
              ((ArithmeticFunction.moebius pq.1 : ℂ) / (Nat.totient pq.1 : ℂ)) ^ 2
                * e (-((n : ℝ) * ((pq.2 : ℝ) / (pq.1 : ℝ)))))
        - ∑ pq ∈ anchors P,
            ((ArithmeticFunction.moebius pq.1 : ℂ) / (Nat.totient pq.1 : ℂ)) ^ 2 * rhoTail N Q n pq := by
  rw [coeffModel_eq_arc, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro pq _
  rw [anchor_arc_eq N n ((pq.2 : ℝ) / (pq.1 : ℝ)) (arc Q pq)
      ((Metric.isClosed_closedBall.measurableSet).inter measurableSet_Ioc) Set.inter_subset_right]
  unfold rhoTail
  ring

open scoped Classical in
/-- Anchors whose Farey arc actually meets `(0,1]` (`a/q ∈ [0,1]`); the `[-P,2P]` anchors with
    `a/q ∉ [0,1]` have empty arcs and contribute `0` to `coeffModel`. -/
noncomputable def neAnchors (P Q : ℕ) : Finset (ℕ × ℤ) :=
  (anchors P).filter (fun pq => (arc Q pq).Nonempty)

open scoped Classical in
/-- **Nonempty-arc split** of the arc-tail: `coeffModel(n) = r_N·(∑_{ne}(μ/φ)²e(-na/q)) −
    ∑_{ne}(μ/φ)²ρ_q(n)`, summing only over anchors whose arc meets `(0,1]` (empty arcs give `∫_∅=0`,
    dropped via `sum_subset`). The main sum `∑_{ne}(μ/φ)²e(-na/q)` over each fixed `q` runs over a
    reduced residue system mod `q` (`a ∈ [1,q−1]`, `(a,q)=1`) → `c_q(n)`, so it reconciles to
    `singSeries_C P n` (Ramanujan, `main_sum_eq_singSeries`); then `h1 = −Re E`. -/
lemma coeffModel_ne_split (N P Q n : ℕ) :
    coeffModel N P Q n
      = (((Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 = n)).card : ℂ)
          * (∑ pq ∈ neAnchors P Q,
              ((ArithmeticFunction.moebius pq.1 : ℂ) / (Nat.totient pq.1 : ℂ)) ^ 2
                * e (-((n : ℝ) * ((pq.2 : ℝ) / (pq.1 : ℝ)))))
        - ∑ pq ∈ neAnchors P Q,
            ((ArithmeticFunction.moebius pq.1 : ℂ) / (Nat.totient pq.1 : ℂ)) ^ 2 * rhoTail N Q n pq := by
  have hzero : ∀ pq ∈ anchors P, pq ∉ neAnchors P Q →
      ((ArithmeticFunction.moebius pq.1 : ℂ) / (Nat.totient pq.1 : ℂ)) ^ 2
        * ∫ α in arc Q pq,
          (∑ k ∈ Finset.range N, e ((k : ℝ) * (α - (pq.2 : ℝ) / (pq.1 : ℝ)))) ^ 2 * e (-((n : ℝ) * α))
        = 0 := by
    intro pq hpq hnf
    rw [neAnchors, Finset.mem_filter, not_and] at hnf
    have hempty : arc Q pq = ∅ := Set.not_nonempty_iff_eq_empty.mp (hnf hpq)
    rw [hempty, Measure.restrict_empty, integral_zero_measure, mul_zero]
  rw [coeffModel_eq_arc, ← Finset.sum_subset (Finset.filter_subset _ _) hzero,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro pq _
  rw [anchor_arc_eq N n ((pq.2 : ℝ) / (pq.1 : ℝ)) (arc Q pq)
      ((Metric.isClosed_closedBall.measurableSet).inter measurableSet_Ioc) Set.inter_subset_right]
  unfold rhoTail
  ring





/-- **Ideal main term as a single integral**: `r_N·𝔖_P(n) = ∫_{(0,1]} Ψ_ideal·e(-nα)`. Via
    `full_arc_eq` per canonical Farey fraction (`∫_{(0,1]}D_N(α−a/q)²e = e(-na/q)·r_N`) + nested
    integral linearity (`integral_finset_sum` × 2, `integral_const_mul`). The `∫_{(0,1]}`-form ideal
    main term — pairs with `coeffModel_as_integral` so the arc-tail error `coeffModel − r_N𝔖_P` is a
    SINGLE Fourier coefficient of `1_{⋃arc}Φ − Ψ_ideal`, bounded by ONE `bessel_minor`. -/
lemma mainInt_eq (N P n : ℕ) :
    (((Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 = n)).card : ℂ) * singSeriesC P n
      = ∫ α in Set.Ioc (0:ℝ) 1, PsiIdeal N P α * e (-((n : ℝ) * α)) := by
  have hcont : ∀ (c : ℝ), Continuous
      (fun α : ℝ => (∑ k ∈ Finset.range N, e ((k : ℝ) * (α - c))) ^ 2 * e (-((n : ℝ) * α))) := by
    intro c; simp only [e]; fun_prop
  have hinner : ∀ q : ℕ,
      (∫ α in Set.Ioc (0:ℝ) 1,
        (∑ a ∈ redRes q, (∑ k ∈ Finset.range N, e ((k : ℝ) * (α - (a : ℝ) / (q : ℝ)))) ^ 2)
          * e (-((n : ℝ) * α)))
      = (((Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 = n)).card : ℂ) * cRamC q n := by
    intro q
    simp only [Finset.sum_mul]
    rw [integral_finset_sum (redRes q)
      (f := fun (a : ℕ) (α : ℝ) =>
        (∑ k ∈ Finset.range N, e ((k : ℝ) * (α - (a : ℝ) / (q : ℝ)))) ^ 2 * e (-((n : ℝ) * α)))
      (fun a _ => (hcont ((a : ℝ) / (q : ℝ))).integrableOn_Ioc)]
    rw [cRamC, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [full_arc_eq N n ((a : ℝ) / (q : ℝ)), mul_comm]
  rw [singSeriesC, Finset.mul_sum]
  simp only [PsiIdeal, Finset.sum_mul]
  rw [integral_finset_sum (Finset.Icc 1 P)
    (f := fun (q : ℕ) (α : ℝ) =>
      ((ArithmeticFunction.moebius q : ℂ) / (Nat.totient q : ℂ)) ^ 2
        * (∑ a ∈ redRes q, (∑ k ∈ Finset.range N, e ((k : ℝ) * (α - (a : ℝ) / (q : ℝ)))) ^ 2)
        * e (-((n : ℝ) * α)))
    (fun q _ => by apply Continuous.integrableOn_Ioc; simp only [e]; fun_prop)]
  apply Finset.sum_congr rfl
  intro q _
  simp only [mul_assoc]
  rw [integral_const_mul, hinner q]
  ring


/-- **coeffModel as a single `(0,1]`-integral of an `n`-independent kernel**:
    `coeffModel(n) = ∫_{(0,1]} Φ(α)·e(-nα)`. Each anchor arc integral extends to `(0,1]` via its
    indicator (`integral_indicator`, `arc ⊆ (0,1]`), then linearity (`integral_finset_sum`) pulls the
    finite sum out and factors `e` (`Finset.sum_mul`). With `mainInt_eq`, the arc-tail error
    `coeffModel − r_N𝔖_P = ∫_{(0,1]}(Φ − Ψ_ideal)·e(-nα)` is a single Fourier coefficient of the
    `n`-independent `Φ − Ψ_ideal` → one Bessel inequality. -/
lemma coeffModel_eq_intPhi (N P Q n : ℕ) :
    coeffModel N P Q n = ∫ α in Set.Ioc (0:ℝ) 1, PhiArc N P Q α * e (-((n : ℝ) * α)) := by
  rw [coeffModel_eq_arc]
  have hmeas : ∀ pq : ℕ × ℤ, MeasurableSet (arc Q pq) :=
    fun pq => (Metric.isClosed_closedBall.measurableSet).inter measurableSet_Ioc
  have hsub : ∀ pq : ℕ × ℤ, arc Q pq ⊆ Set.Ioc (0:ℝ) 1 := fun pq => Set.inter_subset_right
  have hterm : ∀ pq : ℕ × ℤ,
      ((ArithmeticFunction.moebius pq.1 : ℂ) / (Nat.totient pq.1 : ℂ)) ^ 2
        * ∫ α in arc Q pq,
          (∑ k ∈ Finset.range N, e ((k : ℝ) * (α - (pq.2 : ℝ) / (pq.1 : ℝ)))) ^ 2 * e (-((n : ℝ) * α))
      = ∫ α in Set.Ioc (0:ℝ) 1,
          (arc Q pq).indicator (fun α => ((ArithmeticFunction.moebius pq.1 : ℂ) / (Nat.totient pq.1 : ℂ)) ^ 2
            * (∑ k ∈ Finset.range N, e ((k : ℝ) * (α - (pq.2 : ℝ) / (pq.1 : ℝ)))) ^ 2) α
            * e (-((n : ℝ) * α)) := by
    intro pq
    rw [← integral_const_mul, ← MeasureTheory.integral_indicator (hmeas pq),
        ← MeasureTheory.integral_indicator measurableSet_Ioc]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro α
    by_cases hα : α ∈ arc Q pq
    · rw [Set.indicator_of_mem hα, Set.indicator_of_mem (hsub pq hα),
        Set.indicator_of_mem hα]; ring
    · by_cases hαI : α ∈ Set.Ioc (0:ℝ) 1
      · rw [Set.indicator_of_notMem hα, Set.indicator_of_mem hαI,
          Set.indicator_of_notMem hα, zero_mul]
      · rw [Set.indicator_of_notMem hα, Set.indicator_of_notMem hαI]
  have hintegr : ∀ pq ∈ anchors P, IntegrableOn (fun α =>
      (arc Q pq).indicator (fun α => ((ArithmeticFunction.moebius pq.1 : ℂ) / (Nat.totient pq.1 : ℂ)) ^ 2
        * (∑ k ∈ Finset.range N, e ((k : ℝ) * (α - (pq.2 : ℝ) / (pq.1 : ℝ)))) ^ 2) α
        * e (-((n : ℝ) * α))) (Set.Ioc (0:ℝ) 1) := by
    intro pq _
    have hrw : (fun α => (arc Q pq).indicator
        (fun α => ((ArithmeticFunction.moebius pq.1 : ℂ) / (Nat.totient pq.1 : ℂ)) ^ 2
          * (∑ k ∈ Finset.range N, e ((k : ℝ) * (α - (pq.2 : ℝ) / (pq.1 : ℝ)))) ^ 2) α
          * e (-((n : ℝ) * α)))
        = (arc Q pq).indicator (fun α =>
            ((ArithmeticFunction.moebius pq.1 : ℂ) / (Nat.totient pq.1 : ℂ)) ^ 2
              * (∑ k ∈ Finset.range N, e ((k : ℝ) * (α - (pq.2 : ℝ) / (pq.1 : ℝ)))) ^ 2
              * e (-((n : ℝ) * α))) := by
      funext α
      by_cases hα : α ∈ arc Q pq
      · rw [Set.indicator_of_mem hα, Set.indicator_of_mem hα]
      · rw [Set.indicator_of_notMem hα, Set.indicator_of_notMem hα, zero_mul]
    rw [hrw]
    apply MeasureTheory.IntegrableOn.indicator ?_ (hmeas pq)
    apply Continuous.integrableOn_Ioc; simp only [e]; fun_prop
  rw [Finset.sum_congr rfl (fun pq _ => hterm pq), ← MeasureTheory.integral_finset_sum _ hintegr]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro α
  simp only [PhiArc]
  rw [Finset.sum_mul]

/-- `Φ·e(-nα)` is integrable on `(0,1]` (finite sum of indicator·continuous terms). -/
lemma PhiArc_integrableOn (N P Q n : ℕ) :
    IntegrableOn (fun α => PhiArc N P Q α * e (-((n : ℝ) * α))) (Set.Ioc (0:ℝ) 1) := by
  have hmeas : ∀ pq : ℕ × ℤ, MeasurableSet (arc Q pq) :=
    fun pq => (Metric.isClosed_closedBall.measurableSet).inter measurableSet_Ioc
  have hrw : (fun α => PhiArc N P Q α * e (-((n : ℝ) * α)))
      = fun α => ∑ pq ∈ anchors P,
          ((arc Q pq).indicator (fun α => ((ArithmeticFunction.moebius pq.1 : ℂ) / (Nat.totient pq.1 : ℂ)) ^ 2
            * (∑ k ∈ Finset.range N, e ((k : ℝ) * (α - (pq.2 : ℝ) / (pq.1 : ℝ)))) ^ 2) α
            * e (-((n : ℝ) * α))) := by
    funext α; simp only [PhiArc]; rw [Finset.sum_mul]
  rw [IntegrableOn, hrw]
  apply MeasureTheory.integrable_finset_sum
  intro pq _
  have hrw2 : (fun α => (arc Q pq).indicator
      (fun α => ((ArithmeticFunction.moebius pq.1 : ℂ) / (Nat.totient pq.1 : ℂ)) ^ 2
        * (∑ k ∈ Finset.range N, e ((k : ℝ) * (α - (pq.2 : ℝ) / (pq.1 : ℝ)))) ^ 2) α
        * e (-((n : ℝ) * α)))
      = (arc Q pq).indicator (fun α =>
          ((ArithmeticFunction.moebius pq.1 : ℂ) / (Nat.totient pq.1 : ℂ)) ^ 2
            * (∑ k ∈ Finset.range N, e ((k : ℝ) * (α - (pq.2 : ℝ) / (pq.1 : ℝ)))) ^ 2
            * e (-((n : ℝ) * α))) := by
    funext α
    by_cases hα : α ∈ arc Q pq
    · rw [Set.indicator_of_mem hα, Set.indicator_of_mem hα]
    · rw [Set.indicator_of_notMem hα, Set.indicator_of_notMem hα, zero_mul]
  rw [hrw2]
  exact (MeasureTheory.IntegrableOn.indicator
    (by apply Continuous.integrableOn_Ioc; simp only [e]; fun_prop) (hmeas pq))

/-- **Arc-tail error as a single Fourier coefficient**: `coeffModel(n) − r_N·𝔖_P(n) =
    ∫_{(0,1]} (Φ − Ψ_ideal)·e(-nα)`. Combines `coeffModel_eq_intPhi` + `mainInt_eq` + `integral_sub`
    (both `Φ·e`, `Ψ_ideal·e` integrable) + factoring `e`. The arc-tail L² error is now
    `∑_n |∫(Φ−Ψ_ideal)e(-nα)|²`, bounded by ONE Bessel inequality by `∫|Φ−Ψ_ideal|²`. -/
lemma arcTailError_eq_int (N P Q n : ℕ) :
    coeffModel N P Q n
        - (((Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 = n)).card : ℂ) * singSeriesC P n
      = ∫ α in Set.Ioc (0:ℝ) 1, (PhiArc N P Q α - PsiIdeal N P α) * e (-((n : ℝ) * α)) := by
  rw [coeffModel_eq_intPhi, mainInt_eq, ← integral_sub (PhiArc_integrableOn N P Q n) ?_]
  · apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro α; ring
  · apply Continuous.integrableOn_Ioc; simp only [PsiIdeal, e]; fun_prop

/-- `‖e x‖ = 1` (unit character). -/
lemma norm_e (x : ℝ) : ‖e x‖ = 1 := by
  rw [e, Complex.norm_exp]
  have : (2 * (Real.pi : ℂ) * Complex.I * (x : ℝ)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [this, Real.exp_zero]

/-- `‖D_N(x)‖ = ‖∑_{k<N} e(kx)‖ ≤ N`. -/
lemma dirichlet_norm_le (N : ℕ) (x : ℝ) :
    ‖∑ k ∈ Finset.range N, e ((k : ℝ) * x)‖ ≤ (N : ℝ) := by
  calc ‖∑ k ∈ Finset.range N, e ((k : ℝ) * x)‖
      ≤ ∑ k ∈ Finset.range N, ‖e ((k : ℝ) * x)‖ := norm_sum_le _ _
    _ = ∑ k ∈ Finset.range N, (1 : ℝ) := by
        apply Finset.sum_congr rfl; intro k _; exact norm_e _
    _ = (N : ℝ) := by simp

/-- `Φ − Ψ_ideal` is uniformly bounded (`‖D_N‖≤N`, `‖(μ/φ)²‖`-weighted finite sums). -/
lemma PhiSubPsi_bdd (N P Q : ℕ) :
    ∃ C : ℝ, ∀ α : ℝ, ‖PhiArc N P Q α - PsiIdeal N P α‖ ≤ C := by
  have hD2 : ∀ c : ℝ, ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * (c))) ^ 2‖ ≤ (N : ℝ) ^ 2 := by
    intro c
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (dirichlet_norm_le N c) 2
  refine ⟨(∑ pq ∈ anchors P, ‖((ArithmeticFunction.moebius pq.1 : ℂ) / (Nat.totient pq.1 : ℂ)) ^ 2‖ * (N : ℝ) ^ 2)
        + (∑ q ∈ Finset.Icc 1 P, ‖((ArithmeticFunction.moebius q : ℂ) / (Nat.totient q : ℂ)) ^ 2‖
            * ((redRes q).card * (N : ℝ) ^ 2)), fun α => ?_⟩
  refine le_trans (norm_sub_le _ _) (add_le_add ?_ ?_)
  · simp only [PhiArc]
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum ?_)
    intro pq _
    refine le_trans (norm_indicator_le_norm_self _ _) ?_
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hD2 _) (norm_nonneg _)
  · simp only [PsiIdeal]
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum ?_)
    intro q _
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    refine le_trans (norm_sum_le _ _) ?_
    calc ∑ a ∈ redRes q, ‖(∑ k ∈ Finset.range N, e ((k : ℝ) * (α - (a : ℝ) / (q : ℝ)))) ^ 2‖
        ≤ ∑ a ∈ redRes q, (N : ℝ) ^ 2 := Finset.sum_le_sum (fun a _ => hD2 _)
      _ = ((redRes q).card : ℝ) * (N : ℝ) ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]

/-- `‖Φ − Ψ_ideal‖²` is integrable on `(0,1]` (bounded × finite measure) — the finite RHS of the
    arc-tail Bessel bound. -/
lemma PhiSubPsi_sq_integrableOn (N P Q : ℕ) :
    IntegrableOn (fun α => ‖PhiArc N P Q α - PsiIdeal N P α‖ ^ 2) (Set.Ioc (0:ℝ) 1) := by
  obtain ⟨C, hC⟩ := PhiSubPsi_bdd N P Q
  have hphi : AEStronglyMeasurable (fun α => PhiArc N P Q α)
      (volume.restrict (Set.Ioc (0:ℝ) 1)) := by
    have heq : (fun α => PhiArc N P Q α)
        = ∑ pq ∈ anchors P, (arc Q pq).indicator
            (fun α => ((ArithmeticFunction.moebius pq.1 : ℂ) / (Nat.totient pq.1 : ℂ)) ^ 2
              * (∑ k ∈ Finset.range N, e ((k : ℝ) * (α - (pq.2 : ℝ) / (pq.1 : ℝ)))) ^ 2) := by
      funext α; simp only [PhiArc, Finset.sum_apply]
    rw [heq]
    apply Finset.aestronglyMeasurable_sum
    intro pq _
    apply AEStronglyMeasurable.indicator
    · apply Continuous.aestronglyMeasurable; simp only [e]; fun_prop
    · exact (Metric.isClosed_closedBall.measurableSet).inter measurableSet_Ioc
  have hpsi : AEStronglyMeasurable (fun α => PsiIdeal N P α)
      (volume.restrict (Set.Ioc (0:ℝ) 1)) := by
    apply Continuous.aestronglyMeasurable; simp only [PsiIdeal, e]; fun_prop
  have hf : AEStronglyMeasurable (fun α => ‖PhiArc N P Q α - PsiIdeal N P α‖ ^ 2)
      (volume.restrict (Set.Ioc (0:ℝ) 1)) :=
    (continuous_norm.pow 2).comp_aestronglyMeasurable (hphi.sub hpsi)
  apply MeasureTheory.Integrable.mono' (g := fun _ => C ^ 2)
    (continuous_const.integrableOn_Ioc) hf
  apply Filter.Eventually.of_forall
  intro α
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (hC α) 2


/-- **Arc-tail L² error ≤ ∫‖Φ−Ψ_ideal‖²** — the single Bessel bound. `∑_{n<M}‖coeffModel(n) −
    r_N𝔖_P(n)‖² ≤ ∫_{(0,1]}‖Φ−Ψ_ideal‖²`: rewrite each summand by `arcTailError_eq_int` (making it a
    Fourier coefficient of the `n`-independent `Φ−Ψ_ideal`), then ONE `bessel_Ioc` (L²-integrability
    from `PhiSubPsi_sq_integrableOn`). The arc-tail L² error is now controlled by a single integral —
    remaining: `∫_{(0,1]}‖Φ−Ψ_ideal‖² ≤ εX³` (the Dirichlet-L⁴ major-arc estimate). -/
lemma arcTailError_bessel (N P Q M : ℕ) :
    ∑ n ∈ Finset.range M,
        ‖coeffModel N P Q n
          - (((Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 = n)).card : ℂ) * singSeriesC P n‖ ^ 2
      ≤ ∫ α in Set.Ioc (0:ℝ) 1, ‖PhiArc N P Q α - PsiIdeal N P α‖ ^ 2 := by
  simp_rw [arcTailError_eq_int]
  exact bessel_Ioc (fun α => PhiArc N P Q α - PsiIdeal N P α) (PhiSubPsi_sq_integrableOn N P Q) M

-- ==== Tarithv discharge (= MajorArcMainTerm.Tarith evaluated) ====

noncomputable def Tarithv : ℕ → ℕ → ℝ := fun n q => Tarith n q

theorem Tarithv_apply (n q : ℕ) :
    Tarithv n q = (ArithmeticFunction.moebius q : ℝ) ^ 2 * (cRam q n : ℝ)
      / (Nat.totient q : ℝ) ^ 2 := Tarith_apply n q

theorem Tarithv_zero (n : ℕ) : Tarithv n 0 = 0 := ArithmeticFunction.map_zero

theorem Tarith_summable_v (n : ℕ) (hn : 1 ≤ n) :
    Summable (fun q => ‖Tarithv n q‖) := Tarith_summable n hn

theorem singSeries_eq_sum_Tarithv (P n : ℕ) :
    singSeries P n = ∑ q ∈ Finset.Icc 1 P, Tarithv n q := singSeries_eq_sum_Tarith P n

/-!
# harc truncation assembly (interval large sieve → singular-series tail L²)

Continuation of `MajorArcMainTerm.lean`'s Ramanujan-large-sieve tower, split out so bricks check
fast (the parent file grew to ~80s). Every `axiom` in `section Inputs` is **PROVEN axiom-free in
`MajorArcMainTerm.lean`** and enters here as a labeled cross-file input, to be discharged at the
final Phase-F concatenation (same discipline as `CrossFileInputs` there). The additive character
`e` is the identical top-level definition.
-/

open Finset


section Inputs





end Inputs

/-- **rpow partial-sum bound**: `∑_{q=1}^{X} q^{-4/5} ≤ 5·X^{1/5}`. The analytic estimate that,
    combined with the crude totient bound `φ(q) ≥ q^{3/5}` (so `q/φ(q)³ ≤ q^{-4/5}`), makes the
    `q ≤ X` diagonal truncation error `∑_{q≤X} q(1+log q)/φ³ = O(X^{1/5} log X) = o(X)`. Proved by
    induction; the step rests on concavity of `t ↦ t^{1/5}` (`a⁵−b⁵ ≤ 5a⁴(a−b)` for `0≤b≤a`). -/
lemma sum_rpow_partial (X : ℕ) :
    ∑ q ∈ Finset.Icc 1 X, (q : ℝ) ^ (-(4:ℝ)/5) ≤ 5 * (X : ℝ) ^ ((1:ℝ)/5) := by
  induction X with
  | zero => simp
  | succ X ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ X + 1)]
    have hcast : ((X + 1 : ℕ) : ℝ) = (X:ℝ) + 1 := by push_cast; ring
    rw [hcast]
    have hbase : (0:ℝ) < (X:ℝ) + 1 := by positivity
    set a := ((X:ℝ)+1) ^ ((1:ℝ)/5) with ha_def
    set b := (X:ℝ) ^ ((1:ℝ)/5) with hb_def
    have ha_pos : 0 < a := by rw [ha_def]; exact Real.rpow_pos_of_pos hbase _
    have hb0 : 0 ≤ b := by rw [hb_def]; exact Real.rpow_nonneg (by positivity) _
    have ha5 : a^5 = (X:ℝ)+1 := by
      rw [ha_def, ← Real.rpow_natCast (((X:ℝ)+1)^((1:ℝ)/5)) 5, ← Real.rpow_mul hbase.le]
      rw [show (1:ℝ)/5*(5:ℕ) = 1 by push_cast; ring, Real.rpow_one]
    have hb5 : b^5 = (X:ℝ) := by
      rw [hb_def, ← Real.rpow_natCast ((X:ℝ)^((1:ℝ)/5)) 5,
        ← Real.rpow_mul (by positivity : (0:ℝ) ≤ (X:ℝ))]
      rw [show (1:ℝ)/5*(5:ℕ) = 1 by push_cast; ring, Real.rpow_one]
    have hab : b ≤ a := by
      rw [ha_def, hb_def]
      exact Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
    have ha4 : a^4 = ((X:ℝ)+1)^((4:ℝ)/5) := by
      rw [ha_def, ← Real.rpow_natCast (((X:ℝ)+1)^((1:ℝ)/5)) 4, ← Real.rpow_mul hbase.le]
      norm_num
    have hterm_eq : ((X:ℝ)+1)^(-(4:ℝ)/5) = 1/a^4 := by
      rw [ha4, one_div, show (-(4:ℝ)/5) = -((4:ℝ)/5) by ring, Real.rpow_neg hbase.le]
    have h1 : 0 ≤ a := ha_pos.le
    have hcub : (0:ℝ) ≤ 4*a^3+3*a^2*b+2*a*b^2+b^3 := by
      nlinarith [pow_nonneg h1 3, mul_nonneg (pow_nonneg h1 2) hb0,
        mul_nonneg h1 (pow_nonneg hb0 2), pow_nonneg hb0 3]
    have hpoly : a^5 - b^5 ≤ 5*a^4*(a-b) := by
      nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr hab)) hcub]
    have hone : a^5 - b^5 = 1 := by rw [ha5, hb5]; ring
    have ha4pos : 0 < a^4 := pow_pos ha_pos 4
    have hkey : (1:ℝ) ≤ 5*a^4*(a-b) := by linarith [hpoly, hone]
    have hterm_le : ((X:ℝ)+1)^(-(4:ℝ)/5) ≤ 5*(a-b) := by
      rw [hterm_eq, div_le_iff₀ ha4pos]
      nlinarith [hkey]
    linarith [ih, hterm_le]

/-- **Full interval boundary bound**: `∑_{r∈U_q} ∑_{r'∈U_q\{r}} 2/‖e((r−r')/q)−1‖ ≤ φ(q)·q(1+log q)`.
    Sums the per-`r` bound over the `φ(q)` reduced residues. -/
lemma full_boundary_le (q : ℕ) (hq2 : 2 ≤ q) :
    ∑ r ∈ (Finset.range q).filter (fun r => Nat.gcd r q = 1),
        ∑ r' ∈ ((Finset.range q).filter (fun r => Nat.gcd r q = 1)).erase r,
          2 / ‖e ((((r : ℤ) - (r' : ℤ) : ℤ) : ℝ) / (q : ℝ)) - 1‖
      ≤ (Nat.totient q : ℝ) * ((q : ℝ) * (1 + Real.log q)) := by
  set U := (Finset.range q).filter (fun r => Nat.gcd r q = 1) with hU
  have hcard : U.card = Nat.totient q := by
    rw [hU, Nat.totient]
    apply Finset.card_nbij' id id <;> intro x hx <;>
      simp_all [Finset.mem_filter, Nat.Coprime, Nat.gcd_comm]
  calc ∑ r ∈ U, ∑ r' ∈ U.erase r, 2 / ‖e ((((r : ℤ) - (r' : ℤ) : ℤ) : ℝ) / (q : ℝ)) - 1‖
      ≤ ∑ _r ∈ U, (q : ℝ) * (1 + Real.log q) := by
        apply Finset.sum_le_sum; intro r hr
        have hrq : r < q := Finset.mem_range.mp (Finset.mem_filter.mp hr).1
        exact erase_boundary_le q r hq2 hrq
    _ = (Nat.totient q : ℝ) * ((q : ℝ) * (1 + Real.log q)) := by
        rw [Finset.sum_const, hcard, nsmul_eq_mul]

/-- **Interval single-modulus mean square, explicit boundary**: `|∑_{n<N}‖c_q(n)‖² − N·φ(q)| ≤
    φ(q)·q(1+log q)`. The interval Ramanujan mean value with a clean `O(q² log q)` error — the
    off-diagonal boundary is now bounded in closed form. -/
lemma interval_meansq_bound (q N : ℕ) (hq2 : 2 ≤ q) :
    |(∑ n ∈ Finset.range N, ‖ramSum q n‖ ^ 2) - (N : ℝ) * (Nat.totient q)|
      ≤ (Nat.totient q : ℝ) * ((q : ℝ) * (1 + Real.log q)) :=
  le_trans (ramSum_sq_interval_bound q N (by omega)) (full_boundary_le q hq2)

/-- **Dyadic-block mean square**: `|∑_{n∈(X/2,X]}‖c_q(n)‖² − (X−X/2)·φ(q)| ≤ 2·φ(q)·q(1+log q)`,
    from `interval_meansq_bound` at `N=X+1` and `N=X/2+1` via `range(X+1) = range(X/2+1) ⊔ (X/2,X]`
    and the triangle inequality. This is the diagonal term of the truncation over the dyadic block. -/
lemma interval_meansq_Ioc (q X : ℕ) (hq2 : 2 ≤ q) :
    |(∑ n ∈ Finset.Ioc (X / 2) X, ‖ramSum q n‖ ^ 2) - ((X - X / 2 : ℕ) : ℝ) * (Nat.totient q)|
      ≤ 2 * ((Nat.totient q : ℝ) * ((q : ℝ) * (1 + Real.log q))) := by
  have hb1 := interval_meansq_bound q (X + 1) hq2
  have hb2 := interval_meansq_bound q (X / 2 + 1) hq2
  have hunion : Finset.range (X + 1) = Finset.range (X / 2 + 1) ∪ Finset.Ioc (X / 2) X := by
    ext n; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ioc]; omega
  have hdisj : Disjoint (Finset.range (X / 2 + 1)) (Finset.Ioc (X / 2) X) := by
    rw [Finset.disjoint_left]; intro n; simp only [Finset.mem_range, Finset.mem_Ioc]; omega
  have hsplit : ∑ n ∈ Finset.Ioc (X / 2) X, ‖ramSum q n‖ ^ 2
      = (∑ n ∈ Finset.range (X + 1), ‖ramSum q n‖ ^ 2)
        - ∑ n ∈ Finset.range (X / 2 + 1), ‖ramSum q n‖ ^ 2 := by
    rw [hunion, Finset.sum_union hdisj]; ring
  have hcast : ((X - X / 2 : ℕ) : ℝ) = ((X + 1 : ℕ) : ℝ) - ((X / 2 + 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : X / 2 ≤ X)]; push_cast; ring
  rw [hsplit, hcast]
  calc |(∑ n ∈ Finset.range (X + 1), ‖ramSum q n‖ ^ 2
          - ∑ n ∈ Finset.range (X / 2 + 1), ‖ramSum q n‖ ^ 2)
        - (((X + 1 : ℕ) : ℝ) - ((X / 2 + 1 : ℕ) : ℝ)) * (Nat.totient q)|
      = |(∑ n ∈ Finset.range (X + 1), ‖ramSum q n‖ ^ 2 - ((X + 1 : ℕ) : ℝ) * (Nat.totient q))
          + (-(∑ n ∈ Finset.range (X / 2 + 1), ‖ramSum q n‖ ^ 2
              - ((X / 2 + 1 : ℕ) : ℝ) * (Nat.totient q)))| := by congr 1; ring
    _ ≤ |∑ n ∈ Finset.range (X + 1), ‖ramSum q n‖ ^ 2 - ((X + 1 : ℕ) : ℝ) * (Nat.totient q)|
          + |-(∑ n ∈ Finset.range (X / 2 + 1), ‖ramSum q n‖ ^ 2
              - ((X / 2 + 1 : ℕ) : ℝ) * (Nat.totient q))| := abs_add_le _ _
    _ ≤ (Nat.totient q : ℝ) * ((q : ℝ) * (1 + Real.log q))
          + (Nat.totient q : ℝ) * ((q : ℝ) * (1 + Real.log q)) := by
        rw [abs_neg]; exact add_le_add hb1 hb2
    _ = 2 * ((Nat.totient q : ℝ) * ((q : ℝ) * (1 + Real.log q))) := by ring

/-- **Length-capped interval mean square** (`q > N` regime): `∑_{n<N} ‖c_q(n)‖² ≤ N·φ(q)²`, from the
    pointwise `‖c_q(n)‖ ≤ φ(q)`. The `N`-independent boundary of `interval_meansq_bound` is loose when
    `q > N`; this trivial cap suffices for the `q > X` diagonal because the coefficient `μ²/φ⁴` makes
    `∑_{q>X} μ²/φ⁴·Nφ² = N·∑_{q>X} μ²/φ²` converge with an `X^{-1/5}` tail ⇒ `O(X^{4/5}) = o(X)`. -/
lemma interval_meansq_pointwise (q N : ℕ) :
    ∑ n ∈ Finset.range N, ‖ramSum q n‖ ^ 2 ≤ (N : ℝ) * (Nat.totient q : ℝ) ^ 2 := by
  calc ∑ n ∈ Finset.range N, ‖ramSum q n‖ ^ 2
      ≤ ∑ n ∈ Finset.range N, (Nat.totient q : ℝ) ^ 2 := by
        apply Finset.sum_le_sum; intro n _
        have h := ramSum_norm_le q n
        have h0 := norm_nonneg (ramSum q n)
        nlinarith [h, h0]
    _ = (N : ℝ) * (Nat.totient q : ℝ) ^ 2 := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **Length-capped dyadic-block mean square**: `∑_{n∈(X/2,X]} ‖c_q(n)‖² ≤ (X+1)·φ(q)²`. The
    `q > X` diagonal input, matching `interval_meansq_Ioc`'s block shape. -/
lemma interval_meansq_pointwise_Ioc (q X : ℕ) :
    ∑ n ∈ Finset.Ioc (X / 2) X, ‖ramSum q n‖ ^ 2 ≤ ((X + 1 : ℕ) : ℝ) * (Nat.totient q : ℝ) ^ 2 := by
  calc ∑ n ∈ Finset.Ioc (X / 2) X, ‖ramSum q n‖ ^ 2
      ≤ ∑ n ∈ Finset.range (X + 1), ‖ramSum q n‖ ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro n hn; simp only [Finset.mem_Ioc, Finset.mem_range] at *; omega
        · intro n _ _; positivity
    _ ≤ ((X + 1 : ℕ) : ℝ) * (Nat.totient q : ℝ) ^ 2 := interval_meansq_pointwise q (X + 1)

/-- **Finite Minkowski (ℓ² triangle) for sums**: `∑_{n∈I}(∑_{q∈S} f q n)² ≤ (∑_{q∈S}√(∑_{n∈I}(f q n)²))²`.
    Induction on `S` with Cauchy–Schwarz (`Finset.sum_mul_sq_le_sq_mul_sq`). The core of the harc
    truncation Minkowski assembly: it converts the interval L² of a sum-of-`q` into a sum of per-`q`
    interval L² norms, dodging the divergent signed off-diagonal (a self-contained real-analysis lemma). -/
lemma l2_sum_sq_le (I S : Finset ℕ) (f : ℕ → ℕ → ℝ) :
    ∑ n ∈ I, (∑ q ∈ S, f q n) ^ 2 ≤ (∑ q ∈ S, Real.sqrt (∑ n ∈ I, (f q n) ^ 2)) ^ 2 := by
  have key : Real.sqrt (∑ n ∈ I, (∑ q ∈ S, f q n) ^ 2)
      ≤ ∑ q ∈ S, Real.sqrt (∑ n ∈ I, (f q n) ^ 2) := by
    induction S using Finset.induction with
    | empty => simp
    | insert q₀ S hq₀ IH =>
      have hins : ∀ n, (∑ q ∈ insert q₀ S, f q n) = f q₀ n + ∑ q ∈ S, f q n :=
        fun n => Finset.sum_insert hq₀
      have htri : Real.sqrt (∑ n ∈ I, (f q₀ n + ∑ q ∈ S, f q n) ^ 2)
          ≤ Real.sqrt (∑ n ∈ I, (f q₀ n) ^ 2)
            + Real.sqrt (∑ n ∈ I, (∑ q ∈ S, f q n) ^ 2) := by
        have hsa : (0 : ℝ) ≤ ∑ n ∈ I, (f q₀ n) ^ 2 := by positivity
        have hsb : (0 : ℝ) ≤ ∑ n ∈ I, (∑ q ∈ S, f q n) ^ 2 := by positivity
        have hCS := Finset.sum_mul_sq_le_sq_mul_sq I (f q₀) (fun n => ∑ q ∈ S, f q n)
        have hab : ∑ n ∈ I, f q₀ n * (∑ q ∈ S, f q n)
            ≤ Real.sqrt (∑ n ∈ I, (f q₀ n) ^ 2) * Real.sqrt (∑ n ∈ I, (∑ q ∈ S, f q n) ^ 2) := by
          calc ∑ n ∈ I, f q₀ n * (∑ q ∈ S, f q n)
              ≤ |∑ n ∈ I, f q₀ n * (∑ q ∈ S, f q n)| := le_abs_self _
            _ = Real.sqrt ((∑ n ∈ I, f q₀ n * (∑ q ∈ S, f q n)) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
            _ ≤ Real.sqrt ((∑ n ∈ I, (f q₀ n) ^ 2) * (∑ n ∈ I, (∑ q ∈ S, f q n) ^ 2)) :=
                Real.sqrt_le_sqrt hCS
            _ = Real.sqrt (∑ n ∈ I, (f q₀ n) ^ 2) * Real.sqrt (∑ n ∈ I, (∑ q ∈ S, f q n) ^ 2) :=
                Real.sqrt_mul hsa _
        rw [← Real.sqrt_sq (by positivity :
          (0:ℝ) ≤ Real.sqrt (∑ n ∈ I, (f q₀ n) ^ 2) + Real.sqrt (∑ n ∈ I, (∑ q ∈ S, f q n) ^ 2))]
        apply Real.sqrt_le_sqrt
        have hexp : ∑ n ∈ I, (f q₀ n + ∑ q ∈ S, f q n) ^ 2
            = (∑ n ∈ I, (f q₀ n) ^ 2) + 2 * (∑ n ∈ I, f q₀ n * (∑ q ∈ S, f q n))
              + (∑ n ∈ I, (∑ q ∈ S, f q n) ^ 2) := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro n _; ring
        rw [hexp, add_sq, Real.sq_sqrt hsa, Real.sq_sqrt hsb]
        nlinarith [hab]
      calc Real.sqrt (∑ n ∈ I, (∑ q ∈ insert q₀ S, f q n) ^ 2)
          = Real.sqrt (∑ n ∈ I, (f q₀ n + ∑ q ∈ S, f q n) ^ 2) := by
            rw [Finset.sum_congr rfl (fun n _ => by rw [hins n])]
        _ ≤ Real.sqrt (∑ n ∈ I, (f q₀ n) ^ 2)
              + Real.sqrt (∑ n ∈ I, (∑ q ∈ S, f q n) ^ 2) := htri
        _ ≤ Real.sqrt (∑ n ∈ I, (f q₀ n) ^ 2) + ∑ q ∈ S, Real.sqrt (∑ n ∈ I, (f q n) ^ 2) := by
            linarith [IH]
        _ = ∑ q ∈ insert q₀ S, Real.sqrt (∑ n ∈ I, (f q n) ^ 2) := by
            rw [Finset.sum_insert hq₀]
  calc ∑ n ∈ I, (∑ q ∈ S, f q n) ^ 2
      = Real.sqrt (∑ n ∈ I, (∑ q ∈ S, f q n) ^ 2) ^ 2 := (Real.sq_sqrt (by positivity)).symm
    _ ≤ (∑ q ∈ S, Real.sqrt (∑ n ∈ I, (f q n) ^ 2)) ^ 2 :=
        pow_le_pow_left₀ (Real.sqrt_nonneg _) key 2

section TruncationMinkowski





/-- **Uniform finite bound ⇒ tsum bound** (the Minkowski `M→∞` limit): finite Minkowski passed to the
    infinite tail via `HasSum.tendsto_sum_nat` (partial sums → tsum) + `le_of_tendsto'`. -/
lemma l2_tsum_le (I : Finset ℕ) (v : ℕ → ℕ → ℝ) (b : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hvsum : ∀ n ∈ I, Summable (fun q => v q n))
    (hbsum : Summable b) (hbnn : ∀ q, 0 ≤ b q)
    (hfin : ∀ S : Finset ℕ, ∑ n ∈ I, (∑ q ∈ S, v q n) ^ 2 ≤ C * (∑ q ∈ S, b q) ^ 2) :
    ∑ n ∈ I, (∑' q, v q n) ^ 2 ≤ C * (∑' q, b q) ^ 2 := by
  have htend : Filter.Tendsto (fun M => ∑ n ∈ I, (∑ q ∈ Finset.range M, v q n) ^ 2)
      Filter.atTop (nhds (∑ n ∈ I, (∑' q, v q n) ^ 2)) := by
    apply tendsto_finset_sum
    intro n hn
    exact ((hvsum n hn).hasSum.tendsto_sum_nat).pow 2
  apply le_of_tendsto' htend
  intro M
  calc ∑ n ∈ I, (∑ q ∈ Finset.range M, v q n) ^ 2
      ≤ C * (∑ q ∈ Finset.range M, b q) ^ 2 := hfin _
    _ ≤ C * (∑' q, b q) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ hC
        apply pow_le_pow_left₀ (Finset.sum_nonneg (fun q _ => hbnn q)) _ 2
        exact hbsum.sum_le_tsum (Finset.range M) (fun q _ => hbnn q)

/-- **Finite-S truncation bound**: `∑_{n∈(X/2,X]}(∑_{q∈S}T)² ≤ eX·(∑_{q∈S}μ²/φ^{3/2})²`, via the
    finite Minkowski `l2_sum_sq_le` + the per-q bound `tarith_l2_le_all`. Uniform in `S`. -/
lemma tarith_finite_S_le (S : Finset ℕ) (X : ℕ) :
    ∑ n ∈ Finset.Ioc (X / 2) X, (∑ q ∈ S, Tarithv n q) ^ 2
      ≤ Real.exp 1 * (X : ℝ)
        * (∑ q ∈ S, (ArithmeticFunction.moebius q : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ ((3 : ℝ) / 2)) ^ 2 := by
  calc ∑ n ∈ Finset.Ioc (X / 2) X, (∑ q ∈ S, Tarithv n q) ^ 2
      ≤ (∑ q ∈ S, Real.sqrt (∑ n ∈ Finset.Ioc (X / 2) X, (Tarithv n q) ^ 2)) ^ 2 :=
        l2_sum_sq_le _ _ (fun q n => Tarithv n q)
    _ ≤ (∑ q ∈ S, Real.sqrt (Real.exp 1 * (X : ℝ))
          * ((ArithmeticFunction.moebius q : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ ((3 : ℝ) / 2))) ^ 2 := by
        apply pow_le_pow_left₀ (by positivity) _ 2
        exact Finset.sum_le_sum (fun q _ => tarith_l2_le_all q X)
    _ = Real.exp 1 * (X : ℝ)
          * (∑ q ∈ S, (ArithmeticFunction.moebius q : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ ((3 : ℝ) / 2)) ^ 2 := by
        rw [← Finset.mul_sum, mul_pow, Real.sq_sqrt (by positivity)]

/-- **★ Truncation Minkowski assembly (complete)**: `∑_{n∈(X/2,X]}(∑'_{q>P}T(q))²
    ≤ eX·(∑'_{q>P}μ²/φ^{3/2})²`. Instantiates `l2_tsum_le` (finite Minkowski + `M→∞`) with the
    `P<q`-restricted family. The RHS tail `∑'_{q>P}μ²/φ^{3/2} → 0` as `P→∞` makes it `o(X)` — the
    truncation sub-error of `harc`. -/
lemma tarith_tail_l2_le (P X : ℕ) :
    ∑ n ∈ Finset.Ioc (X / 2) X, (∑' q, (if P < q then Tarithv n q else 0)) ^ 2
      ≤ Real.exp 1 * (X : ℝ)
        * (∑' q, (if P < q then
            (ArithmeticFunction.moebius q : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ ((3 : ℝ) / 2) else 0)) ^ 2 := by
  apply l2_tsum_le (Finset.Ioc (X / 2) X)
    (fun q n => if P < q then Tarithv n q else 0)
    (fun q => if P < q then
      (ArithmeticFunction.moebius q : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ ((3 : ℝ) / 2) else 0)
    (Real.exp 1 * (X : ℝ)) (by positivity)
  · intro n hn
    have hn1 : 1 ≤ n := by rw [Finset.mem_Ioc] at hn; omega
    have hs : Summable (fun q => Tarithv n q) := summable_norm_iff.mp (Tarith_summable_v n hn1)
    refine (hs.indicator {q | P < q}).congr (fun q => ?_)
    simp [Set.indicator_apply, Set.mem_setOf_eq]
  · refine Summable.of_nonneg_of_le (fun q => ?_) (fun q => ?_) phi_pow32_summable
    · split <;> positivity
    · split
      · exact le_refl _
      · positivity
  · intro q; split <;> positivity
  · intro S
    have hv : ∀ n, (∑ q ∈ S, if P < q then Tarithv n q else 0)
        = ∑ q ∈ S.filter (fun q => P < q), Tarithv n q := fun n => by rw [Finset.sum_filter]
    have hb : (∑ q ∈ S, if P < q then
        (ArithmeticFunction.moebius q : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ ((3 : ℝ) / 2) else 0)
        = ∑ q ∈ S.filter (fun q => P < q),
            (ArithmeticFunction.moebius q : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ ((3 : ℝ) / 2) := by
      rw [Finset.sum_filter]
    simp_rw [hv]
    rw [hb]
    exact tarith_finite_S_le (S.filter (fun q => P < q)) X

end TruncationMinkowski

section EpsSmall
open Filter Topology

/-- Tail-as-difference: `∑'_q (if P<q then g q else 0) = ∑'g − ∑_{q<P+1} g`. -/
lemma tail_eq_tsum_sub (g : ℕ → ℝ) (hg : Summable g) (P : ℕ) :
    ∑' q, (if P < q then g q else 0) = (∑' q, g q) - ∑ q ∈ Finset.range (P + 1), g q := by
  have h := hg.sum_add_tsum_compl (s := Finset.range (P + 1))
  have hcompl : (↑(Finset.range (P + 1)) : Set ℕ)ᶜ = {q : ℕ | P < q} := by
    ext q; simp only [Finset.coe_range, Set.mem_compl_iff, Set.mem_Iio, Set.mem_setOf_eq, not_lt]
    omega
  rw [hcompl] at h
  have heq : ∑' q, (if P < q then g q else 0) = ∑' i : {q : ℕ | P < q}, g i := by
    rw [_root_.tsum_subtype]
    apply tsum_congr
    intro q
    rw [Set.indicator_apply]
    simp only [Set.mem_setOf_eq]
  rw [heq]; linarith [h]

/-- **Tail → 0**: `∑'_{q>P} μ²/φ^{3/2} → 0` as `P → ∞` (tail of a convergent series). -/
lemma tail_pow32_tendsto_zero :
    Tendsto (fun P => ∑' q, (if P < q then
        (ArithmeticFunction.moebius q : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ ((3 : ℝ) / 2) else 0))
      atTop (𝓝 0) := by
  have hg : Summable (fun q : ℕ => (ArithmeticFunction.moebius q : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ ((3 : ℝ) / 2)) :=
    phi_pow32_summable
  have hpart : Tendsto (fun P => ∑ q ∈ Finset.range (P + 1),
      (ArithmeticFunction.moebius q : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ ((3 : ℝ) / 2)) atTop
      (𝓝 (∑' q, (ArithmeticFunction.moebius q : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ ((3 : ℝ) / 2))) :=
    (hg.hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
  have hfun : (fun P => ∑' q, (if P < q then
        (ArithmeticFunction.moebius q : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ ((3 : ℝ) / 2) else 0))
      = (fun P => (∑' q, (ArithmeticFunction.moebius q : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ ((3 : ℝ) / 2))
          - ∑ q ∈ Finset.range (P + 1), (ArithmeticFunction.moebius q : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ ((3 : ℝ) / 2)) := by
    funext P; exact tail_eq_tsum_sub _ hg P
  rw [hfun]
  have hz : (∑' q, (ArithmeticFunction.moebius q : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ ((3 : ℝ) / 2))
      - (∑' q, (ArithmeticFunction.moebius q : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ ((3 : ℝ) / 2)) = 0 := by ring
  rw [← hz]
  exact Tendsto.sub tendsto_const_nhds hpart

/-- **ε-smallness**: for every `ε>0`, eventually in `P`, `e·(∑'_{q>P}μ²/φ^{3/2})² ≤ ε`. The tail
    `→0` drives the harc truncation sub-error to `o(X)` once `P = P(X) → ∞`. -/
lemma tarith_trunc_eps_small (ε : ℝ) (hε : 0 < ε) :
    ∃ P₀ : ℕ, ∀ P ≥ P₀, Real.exp 1 * (∑' q, (if P < q then
        (ArithmeticFunction.moebius q : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ ((3 : ℝ) / 2) else 0)) ^ 2 ≤ ε := by
  have hcont : Tendsto (fun P => Real.exp 1 * (∑' q, (if P < q then
      (ArithmeticFunction.moebius q : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ ((3 : ℝ) / 2) else 0)) ^ 2)
      atTop (𝓝 (Real.exp 1 * (0 : ℝ) ^ 2)) :=
    Tendsto.const_mul _ (tail_pow32_tendsto_zero.pow 2)
  rw [show Real.exp 1 * (0 : ℝ) ^ 2 = 0 by ring] at hcont
  rw [Metric.tendsto_atTop] at hcont
  obtain ⟨P₀, hP₀⟩ := hcont ε hε
  refine ⟨P₀, fun P hP => ?_⟩
  have hd := hP₀ P hP
  rw [Real.dist_eq, sub_zero] at hd
  have hnn : (0 : ℝ) ≤ Real.exp 1 * (∑' q, (if P < q then
      (ArithmeticFunction.moebius q : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ ((3 : ℝ) / 2) else 0)) ^ 2 := by
    positivity
  rw [abs_of_nonneg hnn] at hd
  linarith

end EpsSmall

section TruncFinal
open Filter Topology

/-- **Truncation sub-error** (the `l2_error_triangle` input `h2`, in tail form): for a bounded weight
    `rN` (`|rN| ≤ X+1`) and a cutoff `Pf → ∞`, `∑_{n∈(X/2,X]}((∑'_{q>Pf X}T)·rN)² ≤ εX³` eventually.
    Combines the Minkowski bound (`tarith_tail_l2_le`) + ε-smallness (`tarith_trunc_eps_small`) +
    `rN² ≤ (X+1)² ≤ 4X²`. The truncation half of `harc` is now a single, fully-proven inequality. -/
lemma trunc_sub_error (rN : ℕ → ℕ → ℝ) (Pf : ℕ → ℕ)
    (hrN : ∀ X : ℕ, ∀ n ∈ Finset.Ioc (X / 2) X, (rN X n) ^ 2 ≤ ((X : ℝ) + 1) ^ 2)
    (hPf : Tendsto Pf atTop atTop) :
    ∀ ε : ℝ, 0 < ε → ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      ∑ n ∈ Finset.Ioc (X / 2) X, ((∑' q, (if Pf X < q then Tarithv n q else 0)) * rN X n) ^ 2
        ≤ ε * (X : ℝ) ^ 3 := by
  intro ε hε
  obtain ⟨P₀, hP₀⟩ := tarith_trunc_eps_small (ε / 8) (by positivity)
  obtain ⟨X₁, hX₁⟩ := eventually_atTop.mp (tendsto_atTop.mp hPf P₀)
  refine ⟨max X₁ 1, fun X hX => ?_⟩
  have hX1 : X₁ ≤ X := le_trans (le_max_left _ _) hX
  have hXpos : 1 ≤ X := le_trans (le_max_right _ _) hX
  have hXR : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hXpos
  have hPfP : P₀ ≤ Pf X := hX₁ X hX1
  have heps := hP₀ (Pf X) hPfP
  have htail := tarith_tail_l2_le (Pf X) X
  set T2 := (∑' q, (if Pf X < q then
    (ArithmeticFunction.moebius q : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ ((3 : ℝ) / 2) else 0)) ^ 2 with hT2def
  have hstep : ∑ n ∈ Finset.Ioc (X / 2) X, ((∑' q, if Pf X < q then Tarithv n q else 0) * rN X n) ^ 2
      ≤ ((X : ℝ) + 1) ^ 2 * ∑ n ∈ Finset.Ioc (X / 2) X, (∑' q, if Pf X < q then Tarithv n q else 0) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro n hn
    rw [mul_pow]
    nlinarith [hrN X n hn, sq_nonneg (∑' q, if Pf X < q then Tarithv n q else 0)]
  calc ∑ n ∈ Finset.Ioc (X / 2) X, ((∑' q, if Pf X < q then Tarithv n q else 0) * rN X n) ^ 2
      ≤ ((X : ℝ) + 1) ^ 2 * ∑ n ∈ Finset.Ioc (X / 2) X, (∑' q, if Pf X < q then Tarithv n q else 0) ^ 2 :=
        hstep
    _ ≤ ((X : ℝ) + 1) ^ 2 * (Real.exp 1 * (X : ℝ) * T2) :=
        mul_le_mul_of_nonneg_left htail (by positivity)
    _ ≤ ε * (X : ℝ) ^ 3 := by
        have hstep2 : Real.exp 1 * (X : ℝ) * T2 ≤ (X : ℝ) * (ε / 8) := by
          rw [show Real.exp 1 * (X : ℝ) * T2 = (X : ℝ) * (Real.exp 1 * T2) by ring]
          exact mul_le_mul_of_nonneg_left heps (by positivity)
        have hstep3 : ((X : ℝ) + 1) ^ 2 * (Real.exp 1 * (X : ℝ) * T2)
            ≤ ((X : ℝ) + 1) ^ 2 * ((X : ℝ) * (ε / 8)) :=
          mul_le_mul_of_nonneg_left hstep2 (by positivity)
        have hstep4 : ((X : ℝ) + 1) ^ 2 * ((X : ℝ) * (ε / 8)) ≤ ε * (X : ℝ) ^ 3 := by
          have hk : (0 : ℝ) ≤ 7 * (X : ℝ) ^ 3 - 2 * (X : ℝ) ^ 2 - (X : ℝ) := by
            nlinarith [mul_nonneg (sub_nonneg.mpr hXR) (sq_nonneg (X : ℝ)),
              mul_nonneg (sub_nonneg.mpr hXR) (show (0:ℝ) ≤ (X:ℝ) by linarith), hXR]
          nlinarith [mul_nonneg hε.le hk]
        linarith [hstep3, hstep4]

end TruncFinal

section SingSeriesBridge




/-- **Singular-series tail bridge**: `∑'_q (if P<q then T(q) else 0) = 𝔖(n) − 𝔖_P(n)` for `n ≥ 1`.
    Connects `trunc_sub_error`'s tail form to `g − h = (𝔖_P − 𝔖)·rN` of `l2_error_triangle` (since
    `(𝔖_P − 𝔖)² = (∑'_{q>P}T)²`). Via `singSeries_eq_sum_Tarithv` + `tail_eq_tsum_sub`
    (`∑_{range(P+1)} = ∑_{Icc 1 P}` as `T(0)=0`). -/
lemma singSeries_tail (P n : ℕ) (hn : 1 ≤ n) :
    ∑' q, (if P < q then Tarithv n q else 0) = (∑' q, Tarithv n q) - singSeries P n := by
  have hsummable : Summable (fun q => Tarithv n q) := summable_norm_iff.mp (Tarith_summable_v n hn)
  have hrange : Finset.range (P + 1) = insert 0 (Finset.Icc 1 P) := by
    ext q; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
  have h0notin : (0 : ℕ) ∉ Finset.Icc 1 P := by simp
  have hsplit : ∑ q ∈ Finset.range (P + 1), Tarithv n q = ∑ q ∈ Finset.Icc 1 P, Tarithv n q := by
    rw [hrange, Finset.sum_insert h0notin, Tarithv_zero, zero_add]
  rw [singSeries_eq_sum_Tarithv, tail_eq_tsum_sub (fun q => Tarithv n q) hsummable P, hsplit]

end SingSeriesBridge

/-- The tail bridge in the `Icc`-sum form `harc_proven` consumes. -/
theorem singSeries_tail' (P n : ℕ) (hn : 1 ≤ n) :
    ∑' q, (if P < q then Tarithv n q else 0)
      = (∑' q, Tarithv n q) - ∑ q ∈ Finset.Icc 1 P, Tarithv n q := by
  rw [← singSeries_eq_sum_Tarithv]
  exact singSeries_tail P n hn

section HabB
open MeasureTheory Finset

/-- **harc brick 85: the arc-tail leg of `l2_error_triangle`.** With `P = ⌊(log(X+1))⁹⌋₊`,
    `Q = (X+1)/P`: `∑_{n∈(X/2,X]} (Re coeffModel(n) − r_{X+1}(n)·Re 𝔖_P^ℂ(n))² ≤ εX³`
    eventually. Bessel + the B5 chain + the polylog numerics. -/
lemma h1_arcTail (ε : ℝ) (hε : 0 < ε) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      ∑ n ∈ Finset.Ioc (X / 2) X,
        ((coeffModel (X + 1) (Nat.floor ((Real.log (X + 1 : ℕ)) ^ 9))
            ((X + 1) / Nat.floor ((Real.log (X + 1 : ℕ)) ^ 9)) n).re
          - ((((Finset.range (X + 1) ×ˢ Finset.range (X + 1)).filter
                (fun p => p.1 + p.2 = n)).card : ℝ)
              * (singSeriesC (Nat.floor ((Real.log (X + 1 : ℕ)) ^ 9)) n).re)) ^ 2
        ≤ ε * (X : ℝ) ^ 3 := by
  obtain ⟨N₀, hN₀⟩ := arc_tail_rhs_small (ε / 8) (by positivity)
  obtain ⟨N₂₇, hN₂₇⟩ := polylog_le_self 27 2 (by norm_num)
  refine ⟨max 3 (max N₀ N₂₇), fun X hX => ?_⟩
  have hX3 : 3 ≤ X := le_trans (le_max_left _ _) hX
  have hXN₀ : N₀ ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hX
  have hXN₂₇ : N₂₇ ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hX
  set N : ℕ := X + 1 with hNdef
  have hN0R : (0:ℝ) < (N : ℝ) := by positivity
  set L : ℝ := Real.log N with hLdef
  -- L ≥ 1 from N ≥ 4 > e
  have hL1 : (1:ℝ) ≤ L := by
    rw [hLdef, ← Real.log_exp 1]
    apply Real.log_le_log (Real.exp_pos 1)
    calc Real.exp 1 ≤ 3 :=
          le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))
      _ ≤ (N : ℝ) := by
          have h3X : (3:ℝ) ≤ (X : ℝ) := by exact_mod_cast hX3
          rw [hNdef]
          push_cast
          linarith
  set P : ℕ := Nat.floor (L ^ 9) with hPdef
  have hP1R : (1:ℝ) ≤ (P : ℝ) := by
    have h1 : (1:ℝ) ≤ L ^ 9 := one_le_pow₀ hL1
    have := Nat.lt_floor_add_one (L ^ 9)
    have hfl : (1:ℕ) ≤ P := by
      rw [hPdef]
      exact Nat.le_floor (by exact_mod_cast h1)
    exact_mod_cast hfl
  have hP1 : 1 ≤ P := by exact_mod_cast hP1R
  have hP0R : (0:ℝ) < (P : ℝ) := by linarith
  have hPleL9 : (P : ℝ) ≤ L ^ 9 := Nat.floor_le (by positivity)
  -- 2P³ ≤ N via polylog 27
  have h2L27 : 2 * L ^ 27 ≤ (N : ℝ) := by
    have := hN₂₇ N (by omega)
    exact this
  have h2P3 : 2 * P ^ 3 ≤ N := by
    have hreal : 2 * (P : ℝ) ^ 3 ≤ (N : ℝ) := by
      have hL927 : (L ^ 9) ^ 3 = L ^ 27 := by ring
      have h1 : (P : ℝ) ^ 3 ≤ (L ^ 9) ^ 3 := pow_le_pow_left₀ (by positivity) hPleL9 3
      rw [hL927] at h1
      linarith
    exact_mod_cast hreal
  set Q : ℕ := N / P with hQdef
  have hQ2 : 2 ≤ Q := by
    rw [hQdef]
    rw [Nat.le_div_iff_mul_le (by omega : 0 < P)]
    have hPP3 : P ≤ P ^ 3 := Nat.le_self_pow (by norm_num) P
    calc 2 * P ≤ 2 * P ^ 3 := Nat.mul_le_mul (le_refl 2) hPP3
      _ ≤ N := h2P3
  have hPQ : 2 * P ^ 2 < Q + 1 := by
    have h1 : 2 * P ^ 2 ≤ Q := by
      rw [hQdef, Nat.le_div_iff_mul_le (by omega : 0 < P)]
      nlinarith [h2P3]
    omega
  -- pointwise real-part bridge, then Ioc ⊆ range N
  have hpt : ∀ n : ℕ,
      ((coeffModel N P Q n).re
        - ((((Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 = n)).card : ℝ)
            * (singSeriesC P n).re)) ^ 2
      ≤ ‖coeffModel N P Q n
          - (((Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 = n)).card : ℂ)
            * singSeriesC P n‖ ^ 2 := by
    intro n
    set z : ℂ := coeffModel N P Q n
      - (((Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 = n)).card : ℂ)
        * singSeriesC P n with hzdef
    have hre : (coeffModel N P Q n).re
        - ((((Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 = n)).card : ℝ)
            * (singSeriesC P n).re) = z.re := by
      rw [hzdef, Complex.sub_re]
      congr 1
      rw [show (((Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 = n)).card : ℂ)
          = ((((Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 = n)).card : ℝ) : ℂ)
        from by push_cast; rfl]
      rw [Complex.re_ofReal_mul]
    rw [hre]
    calc z.re ^ 2 = |z.re| ^ 2 := (sq_abs _).symm
      _ ≤ ‖z‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm z) 2
  have hsubset : Finset.Ioc (X / 2) X ⊆ Finset.range N := by
    intro n hn
    rw [Finset.mem_range]
    have := (Finset.mem_Ioc.mp hn).2
    omega
  calc ∑ n ∈ Finset.Ioc (X / 2) X,
      ((coeffModel N P Q n).re
        - ((((Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 = n)).card : ℝ)
            * (singSeriesC P n).re)) ^ 2
      ≤ ∑ n ∈ Finset.Ioc (X / 2) X,
          ‖coeffModel N P Q n
            - (((Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 = n)).card : ℂ)
              * singSeriesC P n‖ ^ 2 := Finset.sum_le_sum (fun n _ => hpt n)
    _ ≤ ∑ n ∈ Finset.range N,
          ‖coeffModel N P Q n
            - (((Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 = n)).card : ℂ)
              * singSeriesC P n‖ ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
        intro n _ _
        positivity
    _ ≤ ∫ α in Set.Ioc (0:ℝ) 1, ‖PhiArc N P Q α - PsiIdeal N P α‖ ^ 2 :=
        arcTailError_bessel N P Q N
    _ = ∫ α in Set.Ioc (0:ℝ) 1, ‖PsiIdeal N P α - PhiArc N P Q α‖ ^ 2 := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro α _
        dsimp only
        rw [norm_sub_rev]
    _ ≤ ((Q : ℝ) + 1) ^ 3 * (8 * (P : ℝ) ^ ((5 : ℝ) / 2))
        + 192 * ((Q : ℝ) + 1) * (P : ℝ) ^ 7 :=
        psi_sub_phi_L2_total N P Q hP1 hQ2 hPQ
    _ ≤ ε / 8 * (N : ℝ) ^ 3 := hN₀ N (by omega)
    _ ≤ ε * (X : ℝ) ^ 3 := by
        have hX1R : (1:ℝ) ≤ (X : ℝ) := by
          have : (1:ℕ) ≤ X := by omega
          exact_mod_cast this
        have hNX : (N : ℝ) = (X : ℝ) + 1 := by rw [hNdef]; push_cast; ring
        have hN2X : (N : ℝ) ≤ 2 * (X : ℝ) := by rw [hNX]; linarith
        have h8 : (N : ℝ) ^ 3 ≤ 8 * (X : ℝ) ^ 3 := by
          calc (N : ℝ) ^ 3 ≤ (2 * (X : ℝ)) ^ 3 :=
              pow_le_pow_left₀ (by positivity) hN2X 3
            _ = 8 * (X : ℝ) ^ 3 := by ring
        calc ε / 8 * (N : ℝ) ^ 3 ≤ ε / 8 * (8 * (X : ℝ) ^ 3) :=
            mul_le_mul_of_nonneg_left h8 (by positivity)
          _ = ε * (X : ℝ) ^ 3 := by ring

/-- The Goldbach kernel count is at most `N`: the first coordinate determines the pair. -/
lemma kernel_card_le (N n : ℕ) :
    (((Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 = n)).card : ℝ)
      ≤ (N : ℝ) := by
  have h : ((Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 = n)).card
      ≤ (Finset.range N).card := by
    apply Finset.card_le_card_of_injOn (fun p => p.1)
    · intro p hp
      have := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
      exact this.1
    · intro p hp q hq hpq
      have hp' := (Finset.mem_filter.mp hp).2
      have hq' := (Finset.mem_filter.mp hq).2
      have : p.1 = q.1 := hpq
      ext
      · exact this
      · omega
  rw [Finset.card_range] at h
  exact_mod_cast h

/-- `X ↦ ⌊(log(X+1))⁹⌋₊` tends to infinity. -/
lemma Pfloor_tendsto :
    Filter.Tendsto (fun X : ℕ => Nat.floor ((Real.log (X + 1 : ℕ)) ^ 9))
      Filter.atTop Filter.atTop := by
  apply tendsto_nat_floor_atTop.comp
  apply (Filter.tendsto_pow_atTop (by norm_num : 9 ≠ 0)).comp
  apply Real.tendsto_log_atTop.comp
  have h1 : Filter.Tendsto (fun X : ℕ => ((X + 1 : ℕ) : ℝ)) Filter.atTop Filter.atTop := by
    apply tendsto_natCast_atTop_atTop.comp
    exact Filter.tendsto_add_atTop_nat 1
  exact h1

-- ==== brick 87: harc PROVEN ====

/-- **harc — the major-arc L² error, PROVEN.** `∑_{n∈(X/2,X]} (Re coeffModel(X+1,P,Q,n)
    − mainTerm(X,n))² ≤ εX³` eventually, where `mainTerm = 𝔖(n)·r_{X+1}(n)` (full singular
    series). Split by `l2_error_triangle` through `g = 𝔖_P·r`: the arc-tail leg is
    `h1_arcTail` (Bessel + B5 chain), the truncation leg is `trunc_sub_error` +
    `singSeries_tail`. -/
theorem harc_proven :
    ∀ ε : ℝ, 0 < ε → ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      ∑ n ∈ Finset.Ioc (X / 2) X,
        ((coeffModel (X + 1) (Nat.floor ((Real.log (X + 1 : ℕ)) ^ 9))
            ((X + 1) / Nat.floor ((Real.log (X + 1 : ℕ)) ^ 9)) n).re
          - (∑' q, Tarithv n q)
              * (((Finset.range (X + 1) ×ˢ Finset.range (X + 1)).filter
                  (fun p => p.1 + p.2 = n)).card : ℝ)) ^ 2
        ≤ ε * (X : ℝ) ^ 3 := by
  have hmain := l2_error_triangle
    (fun X n => (coeffModel (X + 1) (Nat.floor ((Real.log (X + 1 : ℕ)) ^ 9))
        ((X + 1) / Nat.floor ((Real.log (X + 1 : ℕ)) ^ 9)) n).re)
    (fun X n => (((Finset.range (X + 1) ×ˢ Finset.range (X + 1)).filter
        (fun p => p.1 + p.2 = n)).card : ℝ)
      * ∑ q ∈ Finset.Icc 1 (Nat.floor ((Real.log (X + 1 : ℕ)) ^ 9)), Tarithv n q)
    (fun X n => (∑' q, Tarithv n q)
      * (((Finset.range (X + 1) ×ˢ Finset.range (X + 1)).filter
          (fun p => p.1 + p.2 = n)).card : ℝ))
    ?_ ?_
  · exact hmain
  · -- h1: the arc-tail leg, rewritten through singSeriesC_re + Tarithv_apply
    intro ε hε
    obtain ⟨X₀, hX₀⟩ := h1_arcTail ε hε
    refine ⟨X₀, fun X hX => ?_⟩
    have h := hX₀ X hX
    have hrw : ∀ n : ℕ,
        (singSeriesC (Nat.floor ((Real.log (X + 1 : ℕ)) ^ 9)) n).re
          = ∑ q ∈ Finset.Icc 1 (Nat.floor ((Real.log (X + 1 : ℕ)) ^ 9)), Tarithv n q := by
      intro n
      rw [singSeriesC_re]
      apply Finset.sum_congr rfl
      intro q _
      rw [Tarithv_apply]
    calc ∑ n ∈ Finset.Ioc (X / 2) X,
        ((coeffModel (X + 1) (Nat.floor ((Real.log (X + 1 : ℕ)) ^ 9))
            ((X + 1) / Nat.floor ((Real.log (X + 1 : ℕ)) ^ 9)) n).re
          - (((Finset.range (X + 1) ×ˢ Finset.range (X + 1)).filter
              (fun p => p.1 + p.2 = n)).card : ℝ)
            * ∑ q ∈ Finset.Icc 1 (Nat.floor ((Real.log (X + 1 : ℕ)) ^ 9)), Tarithv n q) ^ 2
        = ∑ n ∈ Finset.Ioc (X / 2) X,
          ((coeffModel (X + 1) (Nat.floor ((Real.log (X + 1 : ℕ)) ^ 9))
              ((X + 1) / Nat.floor ((Real.log (X + 1 : ℕ)) ^ 9)) n).re
            - (((Finset.range (X + 1) ×ˢ Finset.range (X + 1)).filter
                (fun p => p.1 + p.2 = n)).card : ℝ)
              * (singSeriesC (Nat.floor ((Real.log (X + 1 : ℕ)) ^ 9)) n).re) ^ 2 := by
          apply Finset.sum_congr rfl
          intro n _
          rw [hrw n]
      _ ≤ ε * (X : ℝ) ^ 3 := h
  · -- h2: the truncation leg via trunc_sub_error + singSeries_tail
    have hrN : ∀ X : ℕ, ∀ n ∈ Finset.Ioc (X / 2) X,
        ((((Finset.range (X + 1) ×ˢ Finset.range (X + 1)).filter
            (fun p => p.1 + p.2 = n)).card : ℝ)) ^ 2 ≤ ((X : ℝ) + 1) ^ 2 := by
      intro X n _
      have h1 := kernel_card_le (X + 1) n
      have h0 : (0:ℝ) ≤ (((Finset.range (X + 1) ×ˢ Finset.range (X + 1)).filter
          (fun p => p.1 + p.2 = n)).card : ℝ) := by positivity
      have hcast : ((X + 1 : ℕ) : ℝ) = (X : ℝ) + 1 := by push_cast; ring
      rw [hcast] at h1
      exact pow_le_pow_left₀ h0 h1 2
    have htrunc := trunc_sub_error
      (fun X n => (((Finset.range (X + 1) ×ˢ Finset.range (X + 1)).filter
          (fun p => p.1 + p.2 = n)).card : ℝ))
      (fun X => Nat.floor ((Real.log (X + 1 : ℕ)) ^ 9)) hrN Pfloor_tendsto
    intro ε hε
    obtain ⟨X₀, hX₀⟩ := htrunc ε hε
    refine ⟨max X₀ 1, fun X hX => ?_⟩
    have hXX₀ : X₀ ≤ X := le_trans (le_max_left _ _) hX
    have hX1 : 1 ≤ X := le_trans (le_max_right _ _) hX
    have h := hX₀ X hXX₀
    calc ∑ n ∈ Finset.Ioc (X / 2) X,
        ((((Finset.range (X + 1) ×ˢ Finset.range (X + 1)).filter
            (fun p => p.1 + p.2 = n)).card : ℝ)
          * ∑ q ∈ Finset.Icc 1 (Nat.floor ((Real.log (X + 1 : ℕ)) ^ 9)), Tarithv n q
          - (∑' q, Tarithv n q)
            * (((Finset.range (X + 1) ×ˢ Finset.range (X + 1)).filter
                (fun p => p.1 + p.2 = n)).card : ℝ)) ^ 2
        = ∑ n ∈ Finset.Ioc (X / 2) X,
          ((∑' q, (if Nat.floor ((Real.log (X + 1 : ℕ)) ^ 9) < q then Tarithv n q else 0))
            * (((Finset.range (X + 1) ×ˢ Finset.range (X + 1)).filter
                (fun p => p.1 + p.2 = n)).card : ℝ)) ^ 2 := by
          apply Finset.sum_congr rfl
          intro n hn
          have hn1 : 1 ≤ n := by
            have := (Finset.mem_Ioc.mp hn).1
            omega
          rw [singSeries_tail' _ n hn1]
          ring
      _ ≤ ε * (X : ℝ) ^ 3 := h

end HabB

set_option maxHeartbeats 1000000

end Principia.Common.Goldbach
