import Mathlib.Analysis.Convex.Segment
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Tactic

/-!
# MathDB 354470 — transition convex hulls can differ for planar similarities

Write-up: `mathdb-open-problems/problems/354470/solution.tex` on the `mathdb-results`
branch of `antoshashakov/Principia-Math-In-Progress`.  It refutes **Conjecture 6.2** of
K. Leśniak, N. Snigireva, F. Strobin and A. Vince, *Transition phenomena for the attractor
of an iterated function system*, Nonlinearity **35** (2022), 5396–5426, p. 5425, which
proposes that the metric convex hulls of the lower and upper transition attractors agree
when every map sends metrically convex sets onto metrically convex sets.

This is the companion of #354469, which refutes Conjecture 6.1 of the same paper.

## The witness

On the plane, with `e = (1,0)` and `J (x,y) = (-y,x)` (so `J² = -I` and `J⁻¹ = -J`),

  `r t = (1+t)/2`,  `eps t = 1 - r t`,
  `f t x = r t • J (x - eps t • e) + eps t • e`,
  `g t x = r t • (-J (x + eps t • e)) - eps t • e`.

Both are similarities of ratio `r t < 1` for `t < 1`, fixing `eps t • e` and `-eps t • e`,
whose limits are `0`; so (H1)–(H3) hold and the lower transition attractor is `{0}`.
Every invertible affine map sends segments to segments, so the conjecture's hypothesis
holds as well.

**But the composition `P t = f t ∘ g t` is a homothety.**  `P_eq` proves

  `P t x = (r t)² • x + eps t • ((1 + (r t)²) • e - (2 * r t) • J e)`,

whose fixed point `p t = ((1+(r t)²)/(1+r t), -2 r t/(1+r t))` tends to `e - J e = (1,-1)`.
Since `p t ∈ A t` for each `t < 1`, every Hausdorff limit of the `A t` contains `(1,-1)`,
while the lower attractor is `{0}` — so the hulls differ.

## What is carried, and what is proved

**Carried** (`Setup`), and only this: that a fixed point of `P t` lies in the attractor
`A t` (the source's contraction-plus-invariance-plus-closedness argument), that `Aup` is a
closed one-sided Hausdorff limit of `A (tseq n)` along some `tseq ↑ 1`, and that the lower
transition attractor is `{0}`.  These are Definition 4.3 of the source and have no Mathlib
counterpart.

**Proved**: the composition identity, that `p t` really is a fixed point, that
`p (tseq n) → (1,-1)`, hence `(1,-1) ∈ Aup`, hence the hulls differ.  Also (H1)–(H3)
directly: `f t` and `g t` fix `±eps t • e`, their ratio is `r t`, and `eps t → 0`.

Note the carried hypothesis is stated as *"every fixed point of `P t` lies in `A t`"*, not
as *"`p t ∈ A t`"*.  That matters: `p_fixed` then has to be proved for the hypothesis to
apply, so the module cannot smuggle in the punchline.

## The weakest reading

`convD S = ⋃_{x,y ∈ S} segment x y` is the source's `conv_d`; since `[x,x] = {x}` it
contains `S`.  The conjecture asserts `convD Alow = convD Aup`, and that is what
`not_conj` refutes — a plain set equality, the weakest form the witness kills.

Python check: `Campaigns/MathDB-Formalization/verify_354470.py`.
-/

namespace Principia.MathDB.P354470

open Filter

/-- Rotation by a right angle. -/
def J (p : ℝ × ℝ) : ℝ × ℝ := (-p.2, p.1)

/-- The base point `e = (1,0)`. -/
def e : ℝ × ℝ := (1, 0)

noncomputable def r (t : ℝ) : ℝ := (1 + t) / 2

noncomputable def eps (t : ℝ) : ℝ := 1 - r t

noncomputable def f (t : ℝ) (x : ℝ × ℝ) : ℝ × ℝ := r t • J (x - eps t • e) + eps t • e

noncomputable def g (t : ℝ) (x : ℝ × ℝ) : ℝ × ℝ := r t • (-J (x + eps t • e)) - eps t • e

noncomputable def P (t : ℝ) (x : ℝ × ℝ) : ℝ × ℝ := f t (g t x)

/-- The fixed point of the homothety `P t`. -/
noncomputable def p (t : ℝ) : ℝ × ℝ :=
  ((1 + r t ^ 2) / (1 + r t), -(2 * r t) / (1 + r t))

theorem J_sq (x : ℝ × ℝ) : J (J x) = -x := by
  simp [J, Prod.ext_iff]

theorem J_e : J e = (0, 1) := by simp [J, e]

theorem eps_eq (t : ℝ) : eps t = (1 - t) / 2 := by unfold eps r; ring

/-! ## (H1)–(H3) -/

theorem f_fixes (t : ℝ) : f t (eps t • e) = eps t • e := by
  simp [f, J]

theorem g_fixes (t : ℝ) : g t (-(eps t • e)) = -(eps t • e) := by
  simp [g, J]

/-- Both maps scale every squared distance by exactly `(r t)²`: they are similarities. -/
theorem f_ratio (t : ℝ) (x y : ℝ × ℝ) :
    (f t x - f t y).1 ^ 2 + (f t x - f t y).2 ^ 2
      = r t ^ 2 * ((x - y).1 ^ 2 + (x - y).2 ^ 2) := by
  simp [f, J]; ring

theorem g_ratio (t : ℝ) (x y : ℝ × ℝ) :
    (g t x - g t y).1 ^ 2 + (g t x - g t y).2 ^ 2
      = r t ^ 2 * ((x - y).1 ^ 2 + (x - y).2 ^ 2) := by
  simp [g, J]; ring

theorem eps_one : eps 1 = 0 := by simp [eps_eq]

theorem r_continuous : Continuous r := by unfold r; fun_prop

/-! ## The composition is a homothety -/

theorem P_eq (t : ℝ) (x : ℝ × ℝ) :
    P t x = r t ^ 2 • x + eps t • ((1 + r t ^ 2) • e - (2 * r t) • J e) := by
  simp [P, f, g, J, e, Prod.ext_iff]
  constructor <;> ring

theorem p_fixed {t : ℝ} (ht0 : 0 ≤ t) (ht : t < 1) : P t (p t) = p t := by
  have hr : r t < 1 := by unfold r; linarith
  have hr0 : 0 < 1 + r t := by unfold r; linarith
  rw [P_eq]
  simp [p, e, J, eps, Prod.ext_iff]
  constructor <;> · field_simp; ring

/-! ## The fixed point converges to `(1,-1)` -/

theorem p_one : p 1 = ((1 : ℝ), (-1 : ℝ)) := by
  unfold p r; norm_num

theorem p_continuousAt : ContinuousAt p 1 := by
  have hden : ContinuousAt (fun t : ℝ => 1 + r t) 1 := by unfold r; fun_prop
  have hne : (1 : ℝ) + r 1 ≠ 0 := by unfold r; norm_num
  refine ContinuousAt.prodMk ?_ ?_
  · exact ContinuousAt.div (by unfold r; fun_prop) hden hne
  · exact ContinuousAt.div (by unfold r; fun_prop) hden hne

theorem p_tendsto {u : ℕ → ℝ} (hu : Tendsto u atTop (nhds 1)) :
    Tendsto (fun n => p (u n)) atTop (nhds ((1 : ℝ), (-1 : ℝ))) := by
  have h := (p_continuousAt.tendsto).comp hu
  rwa [p_one] at h

/-! ## The carried analytic half -/

/-- Everything taken from the source's Definition 4.3 and its contraction argument. -/
structure Setup where
  A : ℝ → Set (ℝ × ℝ)
  Aup : Set (ℝ × ℝ)
  Alow : Set (ℝ × ℝ)
  Alow_eq : Alow = {0}
  /-- Any fixed point of `P t` lies in the attractor at `t`.  Stated for EVERY fixed
  point, so `p_fixed` must be proved before it applies. -/
  fixed_mem : ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ q, P t q = q → q ∈ A t
  tseq : ℕ → ℝ
  tseq_nonneg : ∀ n, 0 ≤ tseq n
  tseq_lt : ∀ n, tseq n < 1
  tseq_tendsto : Tendsto tseq atTop (nhds 1)
  Aup_closed : IsClosed Aup
  /-- One-sided Hausdorff convergence `A (tseq n) → Aup`, which is all that is used. -/
  hausdorff : ∀ ε > (0 : ℝ), ∃ N, ∀ n ≥ N, ∀ z ∈ A (tseq n), ∃ w ∈ Aup, dist z w < ε

namespace Setup

variable (S : Setup)

theorem p_mem (n : ℕ) : p (S.tseq n) ∈ S.A (S.tseq n) :=
  S.fixed_mem _ (S.tseq_nonneg n) (S.tseq_lt n) _
    (p_fixed (S.tseq_nonneg n) (S.tseq_lt n))

/-- **`(1,-1)` lies in every upper transition attractor.** -/
theorem corner_mem : ((1 : ℝ), (-1 : ℝ)) ∈ S.Aup := by
  rw [← S.Aup_closed.closure_eq, Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨N₁, hN₁⟩ := S.hausdorff (ε / 2) (by linarith)
  have hp := p_tendsto S.tseq_tendsto
  rw [Metric.tendsto_atTop] at hp
  obtain ⟨N₂, hN₂⟩ := hp (ε / 2) (by linarith)
  obtain ⟨w, hw, hdw⟩ := hN₁ (max N₁ N₂) (le_max_left _ _) _ (S.p_mem (max N₁ N₂))
  refine ⟨w, hw, ?_⟩
  have := hN₂ (max N₁ N₂) (le_max_right _ _)
  calc dist ((1 : ℝ), (-1 : ℝ)) w
      ≤ dist ((1 : ℝ), (-1 : ℝ)) (p (S.tseq (max N₁ N₂))) + dist (p (S.tseq _)) w :=
        dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := by rw [dist_comm] at this; exact add_lt_add this hdw
    _ = ε := by ring

end Setup

/-! ## The refutation -/

/-- The source's metric convex hull `conv_d S = ⋃_{x,y ∈ S} [x,y]`. -/
def convD (S : Set (ℝ × ℝ)) : Set (ℝ × ℝ) := ⋃ x ∈ S, ⋃ y ∈ S, segment ℝ x y

theorem self_subset_convD {S : Set (ℝ × ℝ)} : S ⊆ convD S := by
  intro x hx
  simp only [convD, Set.mem_iUnion]
  exact ⟨x, hx, x, hx, left_mem_segment ℝ x x⟩

theorem convD_singleton_zero : convD ({0} : Set (ℝ × ℝ)) = {0} := by
  apply Set.Subset.antisymm _ self_subset_convD
  intro z hz
  simp only [convD, Set.mem_iUnion, Set.mem_singleton_iff] at hz
  obtain ⟨x, rfl, y, rfl, hseg⟩ := hz
  simpa using hseg

/-- **Conjecture 6.2 is false**: the two hulls differ. -/
theorem not_conj (S : Setup) : convD S.Alow ≠ convD S.Aup := by
  intro h
  have h1 : ((1 : ℝ), (-1 : ℝ)) ∈ convD S.Aup := self_subset_convD S.corner_mem
  rw [← h, S.Alow_eq, convD_singleton_zero] at h1
  simp [Prod.ext_iff] at h1

end Principia.MathDB.P354470
