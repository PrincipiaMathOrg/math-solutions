/-
Copyright (c) 2026 Principia. All rights reserved.
Released under Apache 2.0.
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith

/-!
# The Schur property of `ℓ¹` — infrastructure

**What this is for.**  `#371629` reduces, in its last step, to: a sequence in `ℓ¹` that is weakly
null is norm null.  Mathlib has **no** `SchurProperty` and no weak-nullity machinery at all — that
was checked, declaration and use site — so the theorem has to be built.  Every other step of that
row is now proved; this is the only input left.

**Why it lives here and not in `Common/` yet.**  Nothing below mentions groups, densities or
measures, so it belongs in `Common/` on the project's own promotion rule.  It is being built in
`MathDB/` while incomplete so that a half-built theorem is not sitting in the shared asset; once the
theorem lands, moving the file is a rename and nothing else, which is why it is a **separate module**
rather than more lines in `Problem371629.lean`.

**Why the hypothesis is indicators and not `ℓ^∞`.**  The source tests against all of `ℓ^∞` and then
remarks that finite-valued functions approximate.  The gliding-hump argument only ever evaluates
against a *set* — it picks the coordinates where the hump is positive — so indicators are both the
weaker hypothesis and the sufficient one.  Step 4 of `#371629` delivers exactly this form.

**The shape of what is coming.**  Suppose `‖fₙ‖₁ ↛ 0`.  Build inductively a subsequence `n₁ < n₂ < …`
and cut points `m₀ < m₁ < …` so that almost all of `f_{n_k}`'s mass sits in the block
`[m_{k−1}, m_k)`.  Two facts drive the induction and they are what this file proves:

* given `n`, a cut point exists beyond which `fₙ`'s tail is small — summability;
* given a cut point `m`, all later `fₙ` are small on `[0, m)` — because each *coordinate* tends to
  zero and a finite sum of nulls is null.

The second is the only place weak nullity is used, and it is used only through single coordinates.
-/

namespace Principia.MathDB.SchurL1

open Filter Topology

/-- The `ℓ¹` norm of a sequence. -/
noncomputable def l1norm (g : ℕ → ℝ) : ℝ := ∑' x, |g x|

/-- **Weak nullity, tested against indicators.**  Weaker than testing against `ℓ^∞`, and all the
gliding hump needs. -/
def WeaklyNullOn (f : ℕ → ℕ → ℝ) : Prop :=
  ∀ A : Set ℕ, Tendsto (fun n => ∑' x, Set.indicator A (f n) x) atTop (𝓝 0)

/-- **Each coordinate tends to zero** — test against a singleton. -/
theorem tendsto_coord {f : ℕ → ℕ → ℝ} (h : WeaklyNullOn f) (j : ℕ) :
    Tendsto (fun n => f n j) atTop (𝓝 0) := by
  have hA := h {j}
  have he : ∀ n, (∑' x, Set.indicator ({j} : Set ℕ) (f n) x) = f n j := by
    intro n
    refine (tsum_eq_single j ?_).trans ?_
    · intro b hb
      simp [Set.indicator_apply, hb]
    · simp [Set.indicator_apply]
  simpa only [he] using hA

/-- **A finite window tends to zero**, in absolute value: a finite sum of nulls is null.  The second
driver of the hump induction — "given a cut point, all later `fₙ` are small before it". -/
theorem tendsto_range_abs_sum {f : ℕ → ℕ → ℝ} (h : WeaklyNullOn f) (m : ℕ) :
    Tendsto (fun n => ∑ x ∈ Finset.range m, |f n x|) atTop (𝓝 0) := by
  have hstep : ∀ x ∈ Finset.range m, Tendsto (fun n => |f n x|) atTop (𝓝 0) := by
    intro x _
    simpa using (tendsto_coord h x).abs
  -- `tendsto_finset_sum` is deprecated in this Mathlib; the live name is `tendsto_finsetSum`.
  simpa using tendsto_finsetSum (Finset.range m) hstep

/-- **A cut point exists beyond which the tail is small** — the first driver of the induction. -/
theorem exists_range_tail_lt {g : ℕ → ℝ} (hg : Summable fun x => |g x|) {ε : ℝ} (hε : 0 < ε) :
    ∃ m, l1norm g - ∑ x ∈ Finset.range m, |g x| < ε := by
  have hsum : Tendsto (fun m => ∑ x ∈ Finset.range m, |g x|) atTop (𝓝 (l1norm g)) :=
    hg.hasSum.tendsto_sum_nat
  have hev : ∀ᶠ m in atTop, l1norm g - ε < ∑ x ∈ Finset.range m, |g x| :=
    hsum.eventually (eventually_gt_nhds (by linarith))
  obtain ⟨m, hm⟩ := hev.exists
  exact ⟨m, by linarith⟩

/-- Partial sums never exceed the norm. -/
theorem range_sum_le_l1norm {g : ℕ → ℝ} (hg : Summable fun x => |g x|) (m : ℕ) :
    ∑ x ∈ Finset.range m, |g x| ≤ l1norm g :=
  hg.sum_le_tsum _ (fun _ _ => abs_nonneg _)

/-- The `ℓ¹` norm is nonnegative. -/
theorem l1norm_nonneg (g : ℕ → ℝ) : 0 ≤ l1norm g :=
  tsum_nonneg fun _ => abs_nonneg _

/-- **The failure hypothesis, in usable form.**  A nonnegative sequence that does not tend to zero
is *frequently* bounded below by a fixed `ε`.

The source passes to a subsequence here.  Nothing is gained by doing so: `∃ᶠ … in atTop` already
*is* the subsequence, and carrying it as a filter statement means the step lemma below can meet it
against an eventual condition with one `Frequently.and_eventually` instead of re-indexing. -/
theorem exists_frequently_of_not_tendsto {u : ℕ → ℝ} (hu : ∀ n, 0 ≤ u n)
    (h : ¬ Tendsto u atTop (𝓝 0)) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ᶠ n in atTop, ε ≤ u n := by
  by_contra hcon
  refine h (Metric.tendsto_atTop.2 fun ε hε => ?_)
  have h1 : ∀ᶠ n in atTop, ¬ (ε ≤ u n) := by
    rw [← Filter.not_frequently]
    exact fun hf => hcon ⟨ε, hε, hf⟩
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 h1
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hu n)]
  exact not_le.1 (hN n hn)

/-- **One step of the hump induction.**  Given how far the index has run (`n₀`) and where the last
block ended (`m₀`), produce the next pair: an index at least `n₀` whose norm is still at least `ε₀`,
which is small on `[0, m₀)`, together with a cut point past `m₀` beyond which its tail is small.

Both halves were proved above — `tendsto_range_abs_sum` for "small before `m₀`", which is the one
and only use of weak nullity, and `exists_range_tail_lt` for the cut point, which uses summability
alone.  What this adds is that the two are satisfiable *simultaneously* with the norm bound, because
an eventual set meets a frequent one.  That is the whole content of the induction step; everything
after it is bookkeeping. -/
theorem exists_step {f : ℕ → ℕ → ℝ} (h : WeaklyNullOn f)
    (hsum : ∀ n, Summable fun x => |f n x|) {ε₀ ε : ℝ} (hε : 0 < ε)
    (hfreq : ∃ᶠ n in atTop, ε₀ ≤ l1norm (f n)) (n₀ m₀ : ℕ) :
    ∃ p : ℕ × ℕ, n₀ ≤ p.1 ∧ m₀ < p.2 ∧ ε₀ ≤ l1norm (f p.1) ∧
      (∑ x ∈ Finset.range m₀, |f p.1 x|) < ε ∧
      l1norm (f p.1) - ∑ x ∈ Finset.range p.2, |f p.1 x| < ε := by
  have hev : ∀ᶠ n in atTop, (∑ x ∈ Finset.range m₀, |f n x|) < ε ∧ n₀ ≤ n :=
    ((tendsto_range_abs_sum h m₀).eventually_lt_const hε).and (eventually_ge_atTop n₀)
  obtain ⟨n, hn, hlt, hge⟩ := (hfreq.and_eventually hev).exists
  obtain ⟨m₁, hm₁⟩ := exists_range_tail_lt (hsum n) hε
  refine ⟨(n, max m₁ (m₀ + 1)), hge, ?_, hn, hlt, ?_⟩
  · exact lt_of_lt_of_le (Nat.lt_succ_self m₀) (le_max_right _ _)
  · refine lt_of_le_of_lt (sub_le_sub_left ?_ _) hm₁
    -- `Finset.range_subset` in this Mathlib is `range n ⊆ s ↔ ∀ x < n, x ∈ s`, not the
    -- range-to-range form; spelling the inclusion out avoids depending on which one it is.
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (fun x hx => Finset.mem_range.2
        (lt_of_lt_of_le (Finset.mem_range.1 hx) (le_max_left _ _)))
      fun _ _ _ => abs_nonneg _

/-- **One sign carries half the mass.**  In any finite block, either the coordinates where `g` is
nonnegative, or the rest, have `|∑ g|` at least half of `∑ |g|`.

This is where the argument is forced to choose a *set* rather than a bounded sequence of signs:
`WeaklyNullOn` tests against indicators, so the sign choice must be made by selecting coordinates.
The price is the factor `2`, and it is the only place the final constant loses anything. -/
theorem exists_sign_half (s : Finset ℕ) (g : ℕ → ℝ) :
    ∃ P ⊆ s, (∑ x ∈ s, |g x|) ≤ 2 * |∑ x ∈ P, g x| := by
  classical
  obtain ⟨P, hPs, hPmem⟩ : ∃ P : Finset ℕ, P ⊆ s ∧ ∀ x, x ∈ P ↔ (x ∈ s ∧ 0 ≤ g x) :=
    ⟨s.filter fun x => 0 ≤ g x, Finset.filter_subset _ _, fun _ => Finset.mem_filter⟩
  have hsplit : (∑ x ∈ s \ P, |g x|) + ∑ x ∈ P, |g x| = ∑ x ∈ s, |g x| :=
    Finset.sum_sdiff hPs
  have hneg : ∀ x ∈ s \ P, g x < 0 := by
    intro x hx
    rw [Finset.mem_sdiff] at hx
    by_contra hc
    exact hx.2 ((hPmem x).2 ⟨hx.1, not_lt.1 hc⟩)
  have hPle : (∑ x ∈ P, |g x|) ≤ |∑ x ∈ P, g x| := by
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun x hx => ?_)) (le_abs_self _)
    exact abs_of_nonneg ((hPmem x).1 hx).2
  have hNle : (∑ x ∈ s \ P, |g x|) ≤ |∑ x ∈ s \ P, g x| := by
    have hz : (∑ x ∈ s \ P, |g x|) + ∑ x ∈ s \ P, g x = 0 := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_eq_zero fun x hx => by rw [abs_of_neg (hneg x hx)]; ring
    have hle : (∑ x ∈ s \ P, g x) ≤ 0 := Finset.sum_nonpos fun x hx => le_of_lt (hneg x hx)
    rw [abs_of_nonpos hle]
    linarith
  rcases le_total (∑ x ∈ s \ P, |g x|) (∑ x ∈ P, |g x|) with hcmp | hcmp
  · exact ⟨P, hPs, by linarith⟩
  · exact ⟨s \ P, Finset.sdiff_subset, by linarith⟩

/-! ### The hump sequences

The step lemma is iterated.  Nothing below is mathematics: it is the observation that a recursion
every stage of which is supplied by `exists_step` produces two strictly increasing sequences.
Packaging them as an *existence* statement rather than a `def` keeps the choice function out of
every downstream type.  The indices are offset by one on purpose — `M 0 = 0` is the left end of the
first block, so block `k` is `Ico (M k) (M (k+1))` with no case split at the start. -/

/-- **The gliding hump exists.**  Two strictly increasing sequences — indices `N` and cut points `M`
with `M 0 = 0` — such that each `f (N (k+1))` still has norm at least `ε₀`, is small on `[0, M k)`,
and has a small tail past `M (k+1)`.  Its mass therefore sits, up to `2ε`, inside the block
`[M k, M (k+1))`; and the blocks are disjoint because `M` is strictly increasing. -/
theorem exists_hump_sequences {f : ℕ → ℕ → ℝ} (h : WeaklyNullOn f)
    (hsum : ∀ n, Summable fun x => |f n x|) {ε₀ ε : ℝ} (hε : 0 < ε)
    (hfreq : ∃ᶠ n in atTop, ε₀ ≤ l1norm (f n)) :
    ∃ N M : ℕ → ℕ, StrictMono N ∧ StrictMono M ∧ M 0 = 0 ∧
      ∀ k, ε₀ ≤ l1norm (f (N (k + 1))) ∧
        (∑ x ∈ Finset.range (M k), |f (N (k + 1)) x|) < ε ∧
        l1norm (f (N (k + 1))) - ∑ x ∈ Finset.range (M (k + 1)), |f (N (k + 1)) x| < ε := by
  classical
  have hspec : ∀ a b : ℕ,
      a ≤ ((exists_step h hsum hε hfreq a b).choose).1 ∧
      b < ((exists_step h hsum hε hfreq a b).choose).2 ∧
      ε₀ ≤ l1norm (f ((exists_step h hsum hε hfreq a b).choose).1) ∧
      (∑ x ∈ Finset.range b, |f ((exists_step h hsum hε hfreq a b).choose).1 x|) < ε ∧
      l1norm (f ((exists_step h hsum hε hfreq a b).choose).1)
        - ∑ x ∈ Finset.range ((exists_step h hsum hε hfreq a b).choose).2,
            |f ((exists_step h hsum hε hfreq a b).choose).1 x| < ε :=
    fun a b => (exists_step h hsum hε hfreq a b).choose_spec
  let Q : ℕ → ℕ × ℕ := fun k =>
    Nat.rec ((0 : ℕ), (0 : ℕ))
      (fun _ p => (exists_step h hsum hε hfreq (p.1 + 1) p.2).choose) k
  have hrec : ∀ k, Q (k + 1) = (exists_step h hsum hε hfreq ((Q k).1 + 1) (Q k).2).choose :=
    fun _ => rfl
  refine ⟨fun k => (Q k).1, fun k => (Q k).2, ?_, ?_, rfl, fun k => ?_⟩
  · refine strictMono_nat_of_lt_succ fun k => ?_
    rw [hrec k]
    exact lt_of_lt_of_le (Nat.lt_succ_self _) (hspec ((Q k).1 + 1) (Q k).2).1
  · refine strictMono_nat_of_lt_succ fun k => ?_
    rw [hrec k]
    exact (hspec ((Q k).1 + 1) (Q k).2).2.1
  · -- NO `rw [hrec k]` here: `refine` left the goal as `(fun k => (Q k).1) (k+1)`, un-beta-reduced,
    -- so the pattern `Q (k+1)` does not occur syntactically.  `exact` checks up to defeq, and
    -- `hrec` is `rfl`, so the rewrite was never needed -- only the two `StrictMono` goals, which
    -- arrive beta-reduced from `strictMono_nat_of_lt_succ`, can use it.
    exact ⟨(hspec ((Q k).1 + 1) (Q k).2).2.2.1, (hspec ((Q k).1 + 1) (Q k).2).2.2.2.1,
      (hspec ((Q k).1 + 1) (Q k).2).2.2.2.2⟩

/-- **The block carries all but `2ε` of the mass.**  The sum over `[a, b)` is the difference of two
partial sums, and each of the two tail hypotheses pins one of them. -/
theorem block_sum_ge {g : ℕ → ℝ} {a b : ℕ} (hab : a ≤ b) {ε₀ ε : ℝ}
    (hnorm : ε₀ ≤ l1norm g) (hbefore : (∑ x ∈ Finset.range a, |g x|) < ε)
    (htail : l1norm g - ∑ x ∈ Finset.range b, |g x| < ε) :
    ε₀ - 2 * ε < ∑ x ∈ Finset.Ico a b, |g x| := by
  have hsplit : (∑ x ∈ Finset.range a, |g x|) + ∑ x ∈ Finset.Ico a b, |g x|
      = ∑ x ∈ Finset.range b, |g x| := by
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico]
    exact Finset.sum_Ico_consecutive _ (Nat.zero_le a) hab
  linarith

/-! ### The set, and the contradiction

`WeaklyNullOn` tests against a *fixed* set, so every hump must be captured by one `A`.  That is what
the blocks are for: they are pairwise disjoint, so `A = ⋃ P k` meets block `k` in exactly `P k`, and
the indicator sum at index `N (k+1)` sees the whole of that block's chosen sign class plus two tails
it can see very little of. -/

/-- An indicator never increases the absolute value. -/
theorem abs_indicator_le {g : ℕ → ℝ} (A : Set ℕ) (x : ℕ) : |Set.indicator A g x| ≤ |g x| := by
  by_cases hx : x ∈ A
  · simp [Set.indicator_of_mem hx]
  · simp [Set.indicator_of_notMem hx, abs_nonneg]

/-- **The triangle inequality for a `tsum` of reals.**  Proved here rather than imported:
`norm_tsum_le_tsum_norm` lives in `Analysis.Normed.Group.InfiniteSum`, which is not in this file's
closure, and pulling that closure in for one inequality costs more than the four lines.

The index is an **arbitrary type**, not `ℕ`.  It was written over `ℕ` first, because that is where
the hump argument needed it, and #371629's sufficiency direction then wanted the same inequality
over the group `G` — a type error, not a mathematical one.  Nothing in the proof ever used the
index. -/
theorem abs_tsum_le {ι : Type*} {u : ι → ℝ} (hu : Summable fun i => |u i|) :
    |∑' i, u i| ≤ ∑' i, |u i| := by
  have hs : Summable u := hu.of_abs
  refine abs_le.2 ⟨?_, hs.tsum_le_tsum (fun i => le_abs_self (u i)) hu⟩
  have h1 := hu.neg.tsum_le_tsum (fun i => neg_abs_le (u i)) hs
  rwa [tsum_neg] at h1

/-- Summability transfers to an indicator. -/
theorem summable_indicator {g : ℕ → ℝ} (hg : Summable fun x => |g x|) (A : Set ℕ) :
    Summable fun x => |Set.indicator A g x| :=
  Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun x => abs_indicator_le A x) hg

/-- **The hump is visible to the indicator test.**  If `g` is small before `a` and has a small tail
past `b`, and `A` meets `[a, b)` in exactly `P`, then the indicator sum over `A` keeps all of that
block's signed mass except the two tails. -/
theorem abs_indicator_tsum_gt {g : ℕ → ℝ} (hg : Summable fun x => |g x|)
    {A : Set ℕ} {P : Finset ℕ} {a b : ℕ} (hab : a ≤ b)
    (hPsub : P ⊆ Finset.Ico a b)
    (hAP : ∀ x ∈ Finset.Ico a b, (x ∈ A ↔ x ∈ P))
    {ε : ℝ} (hbefore : (∑ x ∈ Finset.range a, |g x|) < ε)
    (htail : l1norm g - ∑ x ∈ Finset.range b, |g x| < ε) :
    |∑ x ∈ P, g x| - 2 * ε < |∑' x, Set.indicator A g x| := by
  classical
  have habs := summable_indicator hg A
  have hind : Summable (Set.indicator A g) := habs.of_abs
  have hs1 : Summable fun i => |Set.indicator A g (i + b)| := (summable_nat_add_iff b).2 habs
  have hs2 : Summable fun i => |g (i + b)| := (summable_nat_add_iff b).2 hg
  have hsplit := Summable.sum_add_tsum_nat_add b hind
  have hgs := Summable.sum_add_tsum_nat_add b hg
  have htailbd : |∑' i, Set.indicator A g (i + b)| ≤ ∑' i, |g (i + b)| :=
    le_trans (abs_tsum_le hs1) (hs1.tsum_le_tsum (fun i => abs_indicator_le A (i + b)) hs2)
  have hheadbd : |∑ x ∈ Finset.range a, Set.indicator A g x| ≤ ∑ x ∈ Finset.range a, |g x| :=
    le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun x _ => abs_indicator_le A x)
  have hblock : ∑ x ∈ Finset.Ico a b, Set.indicator A g x = ∑ x ∈ P, g x := by
    rw [← Finset.sum_subset hPsub fun x hx hxP =>
      Set.indicator_of_notMem (fun hA => hxP ((hAP x hx).1 hA)) g]
    exact Finset.sum_congr rfl fun x hx => Set.indicator_of_mem ((hAP x (hPsub hx)).2 hx) g
  have hrange : (∑ x ∈ Finset.range a, Set.indicator A g x)
      + ∑ x ∈ Finset.Ico a b, Set.indicator A g x
      = ∑ x ∈ Finset.range b, Set.indicator A g x := by
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico]
    exact Finset.sum_Ico_consecutive _ (Nat.zero_le a) hab
  have hdiff : (∑ x ∈ P, g x) - ∑' x, Set.indicator A g x
      = -((∑ x ∈ Finset.range a, Set.indicator A g x) + ∑' i, Set.indicator A g (i + b)) := by
    rw [← hsplit, ← hrange, hblock]
    ring
  have hkey : |(∑ x ∈ P, g x)| - |∑' x, Set.indicator A g x|
      ≤ |(∑ x ∈ P, g x) - ∑' x, Set.indicator A g x| := abs_sub_abs_le_abs_sub _ _
  have hbound : |(∑ x ∈ P, g x) - ∑' x, Set.indicator A g x| < 2 * ε := by
    rw [hdiff, abs_neg]
    refine lt_of_le_of_lt (abs_add_le _ _) ?_
    have h1 : |∑ x ∈ Finset.range a, Set.indicator A g x| < ε := lt_of_le_of_lt hheadbd hbefore
    have h2 : |∑' i, Set.indicator A g (i + b)| < ε := by
      refine lt_of_le_of_lt htailbd ?_
      have hl : l1norm g = ∑' x, |g x| := rfl
      rw [hl] at htail
      linarith [hgs]
    linarith
  linarith

/-- **Schur's theorem for `ℓ¹`, in the form `#371629` needs it.**  A sequence in `ℓ¹` that is null
against every indicator is norm null.

Mathlib has no `SchurProperty` and no weak-nullity machinery, so this is built from the ground: the
failure hypothesis becomes a *frequent* lower bound, `exists_hump_sequences` slides a hump along the
coordinates, one sign class is chosen per block, and their union is the single set the hypothesis is
finally tested against.  With `ε = ε₀/10` the surviving mass is `ε₀/5` uniformly in `k`, while the
hypothesis says that same quantity tends to zero. -/
theorem tendsto_l1norm_of_weaklyNullOn {f : ℕ → ℕ → ℝ}
    (hsum : ∀ n, Summable fun x => |f n x|) (h : WeaklyNullOn f) :
    Tendsto (fun n => l1norm (f n)) atTop (𝓝 0) := by
  classical
  by_contra hnot
  obtain ⟨ε₀, hε₀, hfreq⟩ := exists_frequently_of_not_tendsto (fun n => l1norm_nonneg _) hnot
  obtain ⟨N, M, hN, hM, hM0, hstep⟩ :=
    exists_hump_sequences h hsum (show (0 : ℝ) < ε₀ / 10 by linarith) hfreq
  choose P hPsub hPhalf using fun k =>
    exists_sign_half (Finset.Ico (M k) (M (k + 1))) (f (N (k + 1)))
  obtain ⟨A, hAmem⟩ : ∃ A : Set ℕ, ∀ x, x ∈ A ↔ ∃ k, x ∈ P k :=
    ⟨⋃ k, (P k : Set ℕ), fun x => by simp⟩
  have hdisj : ∀ j k : ℕ, j ≠ k → ∀ x, x ∈ Finset.Ico (M j) (M (j + 1)) →
      x ∈ Finset.Ico (M k) (M (k + 1)) → False := by
    intro j k hjk x hxj hxk
    rw [Finset.mem_Ico] at hxj hxk
    rcases lt_or_gt_of_ne hjk with hlt | hlt
    · exact absurd (lt_of_lt_of_le hxj.2 (hM.monotone hlt)) (not_lt.2 hxk.1)
    · exact absurd (lt_of_lt_of_le hxk.2 (hM.monotone hlt)) (not_lt.2 hxj.1)
  have hAP : ∀ k, ∀ x ∈ Finset.Ico (M k) (M (k + 1)), (x ∈ A ↔ x ∈ P k) := by
    intro k x hx
    refine ⟨fun hxA => ?_, fun hxP => (hAmem x).2 ⟨k, hxP⟩⟩
    obtain ⟨j, hj⟩ := (hAmem x).1 hxA
    by_cases hjk : j = k
    · subst hjk
      exact hj
    · exact (hdisj j k hjk x (hPsub j hj) hx).elim
  have hvis : ∀ k, ε₀ / 5 < |∑' x, Set.indicator A (f (N (k + 1))) x| := by
    intro k
    obtain ⟨hnorm, hbefore, htail⟩ := hstep k
    have hab : M k ≤ M (k + 1) := le_of_lt (hM (Nat.lt_succ_self k))
    have hblock : ε₀ - 2 * (ε₀ / 10) < ∑ x ∈ Finset.Ico (M k) (M (k + 1)), |f (N (k + 1)) x| :=
      block_sum_ge hab hnorm hbefore htail
    have h1 := lt_of_lt_of_le hblock (hPhalf k)
    have h2 := abs_indicator_tsum_gt (hsum (N (k + 1))) hab (hPsub k) (hAP k) hbefore htail
    linarith
  have hlim : Tendsto (fun k => ∑' x, Set.indicator A (f (N (k + 1))) x) atTop (𝓝 0) :=
    (h A).comp (hN.tendsto_atTop.comp (tendsto_add_atTop_nat 1))
  have habs : Tendsto (fun k => |∑' x, Set.indicator A (f (N (k + 1))) x|) atTop (𝓝 0) := by
    simpa using hlim.abs
  obtain ⟨k, hk⟩ := (habs.eventually_lt_const (show (0 : ℝ) < ε₀ / 5 by linarith)).exists
  exact absurd hk (not_lt.2 (le_of_lt (hvis k)))

/-! ### Schur on an arbitrary type

The source closes step 5 by remarking that the countable case suffices: every `ℓ¹(G)` vector has
countable support, so the union of the supports of a sequence is a countable set `S`, the whole
sequence lies in `ℓ¹(S)`, and every functional on `ℓ^∞(S)` extends to one on `ℓ^∞(G)`.  That remark
is a theorem, and this is it.

The extension half of the remark **disappears** here, and that is the second dividend of testing
against indicators rather than `ℓ^∞`: a subset of `S` is already a subset of `G`, so there is nothing
to extend.  What remains is pure reindexing — `Function.extend` along an injection `↥S ↪ ℕ`, with
`Function.Injective.tsum_eq` moving each sum between the two index sets.  Every such sum is supported
inside the range of the injection, which is exactly the side condition those lemmas ask for. -/

/-- **Schur's theorem on an arbitrary type.**  No countability hypothesis on `α`: the union of the
supports is countable whatever `α` is, and countability of the index set is all the proof on `ℕ`
ever used. -/
theorem tendsto_l1norm_of_weaklyNullOn_type {α : Type*} {f : ℕ → α → ℝ}
    (hsum : ∀ n, Summable fun x => |f n x|)
    (h : ∀ A : Set α, Tendsto (fun n => ∑' x, Set.indicator A (f n) x) atTop (𝓝 0)) :
    Tendsto (fun n => ∑' x, |f n x|) atTop (𝓝 0) := by
  classical
  -- the union of the supports is countable
  have hsupp : ∀ n, (Function.support (f n)).Countable := by
    intro n
    have hc := (hsum n).countable_support
    have he : (Function.support fun x => |f n x|) = Function.support (f n) := by
      ext x
      simp [Function.mem_support, abs_eq_zero]
    rwa [he] at hc
  obtain ⟨S, hSsub, hSc⟩ : ∃ S : Set α, (∀ n, Function.support (f n) ⊆ S) ∧ S.Countable :=
    ⟨⋃ n, Function.support (f n),
      -- the family must be named: higher-order unification will not guess it from the goal
      fun n => Set.subset_iUnion (fun m => Function.support (f m)) n,
      Set.countable_iUnion hsupp⟩
  haveI : Countable ↥S := hSc.to_subtype
  obtain ⟨e, he⟩ := Countable.exists_injective_nat ↥S
  -- the family transported to `ℕ`, by extension along `e`
  obtain ⟨g, hge, hg0⟩ : ∃ g : ℕ → ℕ → ℝ,
      (∀ n (s : ↥S), g n (e s) = f n s) ∧ (∀ n k, k ∉ Set.range e → g n k = 0) :=
    ⟨fun n => Function.extend e (fun s : ↥S => f n s) (fun _ => 0),
      fun n s => he.extend_apply _ _ s,
      fun n k hk => Function.extend_apply' _ _ _ fun hb => hk hb⟩
  -- every sum in sight is supported where the reindexing lemmas need it
  have hind_supp : ∀ (n : ℕ) (C : Set ℕ),
      Function.support (Set.indicator C (g n)) ⊆ Set.range e := by
    intro n C k hk
    by_contra hr
    refine hk ?_
    rw [Set.indicator_apply]
    by_cases hc : k ∈ C
    · rw [if_pos hc]
      exact hg0 n k hr
    · exact if_neg hc
  have hindf_supp : ∀ (n : ℕ) (C : Set α), Function.support (Set.indicator C (f n)) ⊆ S := by
    intro n C x hx
    refine hSsub n ?_
    rw [Function.mem_support]
    intro h0
    refine hx ?_
    rw [Set.indicator_apply]
    by_cases hc : x ∈ C
    · rw [if_pos hc]
      exact h0
    · exact if_neg hc
  have habs_supp : ∀ n, Function.support (fun k => |g n k|) ⊆ Set.range e := by
    intro n k hk
    by_contra hr
    exact hk (show |g n k| = 0 by rw [hg0 n k hr, abs_zero])
  have habsf_supp : ∀ n, (Function.support fun x => |f n x|) ⊆ S := by
    intro n x hx
    refine hSsub n ?_
    simpa [Function.mem_support, abs_eq_zero] using hx
  -- summability transports
  have hsub : ∀ n, Summable fun s : ↥S => |f n (s : α)| := fun n => (hsum n).subtype _
  have hgsum : ∀ n, Summable fun k => |g n k| := by
    intro n
    refine (he.summable_iff (f := fun k => |g n k|) fun k hk => ?_).1 ?_
    · show |g n k| = 0
      rw [hg0 n k hk, abs_zero]
    · simpa [Function.comp_def, hge n] using hsub n
  -- and so does the norm
  have hnorm : ∀ n, l1norm (g n) = ∑' x, |f n x| := by
    intro n
    have h1 : (∑' s : ↥S, |g n (e s)|) = ∑' k, |g n k| :=
      he.tsum_eq (f := fun k => |g n k|) (habs_supp n)
    have h2 : (∑' s : ↥S, |f n (s : α)|) = ∑' x, |f n x| :=
      tsum_subtype_eq_of_support_subset (habsf_supp n)
    show (∑' k, |g n k|) = ∑' x, |f n x|
    rw [← h1, ← h2]
    exact tsum_congr fun s => by rw [hge n s]
  -- weak nullity transports: a subset of `ℕ` pulls back to a subset of `α`
  have hweak : WeaklyNullOn g := by
    intro B
    have hkey : ∀ n, (∑' k, Set.indicator B (g n) k)
        = ∑' x, Set.indicator {x : α | ∃ hx : x ∈ S, e ⟨x, hx⟩ ∈ B} (f n) x := by
      intro n
      have hmem : ∀ s : ↥S, ((s : α) ∈ {x : α | ∃ hx : x ∈ S, e ⟨x, hx⟩ ∈ B} ↔ e s ∈ B) := by
        intro s
        constructor
        · rintro ⟨hx, hB⟩
          rwa [show (⟨(s : α), hx⟩ : ↥S) = s from Subtype.ext rfl] at hB
        · intro hB
          exact ⟨s.2, by rwa [show (⟨(s : α), s.2⟩ : ↥S) = s from Subtype.ext rfl]⟩
      have hL : (∑' s : ↥S, Set.indicator B (g n) (e s)) = ∑' k, Set.indicator B (g n) k :=
        he.tsum_eq (f := Set.indicator B (g n)) (hind_supp n B)
      have hR : (∑' s : ↥S, Set.indicator {x : α | ∃ hx : x ∈ S, e ⟨x, hx⟩ ∈ B} (f n) (s : α))
          = ∑' x, Set.indicator {x : α | ∃ hx : x ∈ S, e ⟨x, hx⟩ ∈ B} (f n) x :=
        tsum_subtype_eq_of_support_subset (hindf_supp n _)
      rw [← hL, ← hR]
      refine tsum_congr fun s => ?_
      rw [Set.indicator_apply, Set.indicator_apply, hge n s]
      by_cases hb : e s ∈ B
      · rw [if_pos hb, if_pos ((hmem s).2 hb)]
      · rw [if_neg hb, if_neg fun hc => hb ((hmem s).1 hc)]
    simpa [hkey] using h {x : α | ∃ hx : x ∈ S, e ⟨x, hx⟩ ∈ B}
  -- apply the theorem on `ℕ` and read the conclusion back
  have := tendsto_l1norm_of_weaklyNullOn hgsum hweak
  simpa [hnorm] using this

end Principia.MathDB.SchurL1
