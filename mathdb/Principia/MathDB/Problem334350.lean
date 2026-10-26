import Mathlib.Algebra.BigOperators.Ring.Finset
import Principia.Common.BinomialFacts
import Principia.Common.Vandermonde
import Principia.Common.RotheConvolution
import Principia.Common.TruncBinomial
import Principia.Common.ChooseConvolution
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Principia.Common.MonotoneTuples
import Mathlib.Algebra.BigOperators.Fin

set_option maxHeartbeats 1000000

/-!
# MathDB #334350 — Svinin's generalized power-sum identity (SPINE, PARTIAL)

Write-up `mathdb-open-problems/problems/334350/solution.tex`,
*A proof of the generalized power-sum identity, with an extension to every odd function*,
18 September 2026.  Source: A. K. Svinin, *Conjectures Involving a Generalization of the
Sums of Powers of Integers*, Experimental Mathematics **27** (2017), Conjecture 3.1.

The conjecture asserts, for all `n, j ≥ 1` and `k ≥ 0`,

`∑_{1≤λ₁≤⋯≤λ_j≤jn} ∑_i (λ_i − (i−1)n)^{2k+1} = S_{k,j}(n)`,

and the write-up proves the stronger statement with `r ↦ r^{2k+1}` replaced by an ARBITRARY
odd `ψ : ℤ → ℂ`.  The source itself proves only the case `j = 2`.

## What this module contains

Everything here is finite combinatorics — the row was selected precisely because it needs no
theory Mathlib lacks.

**Proved unconditionally:**

* `trunc` — the write-up's display (binomial), the one step of its argument that is not
  counting: `(1−b)^{d+1} · U b d (c+1) + b^{c+1} · U (1−b) c (d+1) = 1` over any commutative
  ring, where `U b d m = ∑_{p<m} C(d+p, p) b^p` truncates the negative binomial series.
  Its driver is `U_step`.
* `main_of_links` — the SPINE: the three named links compose to `LHS = RHS`.
* `link2` — **LINK 2 DISCHARGED.**  Collecting the marked tuples fibrewise by exponent
  (`expo_maps_to`, `LHS_eq_sum_cF`, off `Finset.sum_fiberwise_of_maps_to'`) and folding the
  negative half onto the positive one by oddness (`sum_neg_Icc`, `cF_eq_zero_of_notMem`)
  shows the left side IS the odd part of the exponent distribution paired against `ψ`.
* `link3` — **LINK 3 DISCHARGED**, the same collection on the right side
  (`tuple_sum_maps_to`, `Vt_eq_zero_of_notMem`, `tuple_sum_collect`), after each `e`-tuple's
  range `[e, en]` is widened to the common `[1, jn]`, where `Vt` vanishes off its own range.
* `main_of_link1` — the write-up's Theorem reduced to **one** obligation.

**Carried as a named hypothesis: `Link1` alone**, per the campaign convention that
campaign-working inputs enter as hypotheses rather than axioms.  It is the entire
combinatorial content — `c_r − c_{−r} = d_r` for `r ≥ 1` — and is the remaining work.
`dc` is deliberately stated in the CONJECTURE's own shape, `∑_{e=1}^{j} C(N, j−e)·Vt(e, s)`,
so that `Link3` is pure bookkeeping and the binomial reshaping into the `P(B)` shape that
`trunc` produces sits inside `Link1`, where it is actually needed.  **The row is therefore
NOT counted as fully verified.**

## A note on the source's indexing (215)

The write-up states its truncation lemma with `C(a+q−1, q)` "for positive integers `a, j`".
Transcribed literally, Lean's truncating `ℕ`-subtraction reads `C(−1, 0)` as `C(0,0) = 1`, and
the identity is then FALSE at `a = j = 0` — both sums are empty, so the left side is `0`.  The
Python check caught this; the elaborator could not, since the literal statement typechecks.
The fix here is a change of variables rather than a side hypothesis: `a = c+1`, `j = d+1`
makes every index a genuine sum, so `trunc` carries no degenerate case and no side condition.

## Python value check

`Campaigns/MathDB-Formalization/verify_334350.py`, all seven families by brute force: the
source conjecture for `n, j ≤ 4` and `k ≤ 3`; the odd-`ψ` strengthening against random
rational odd `ψ`; the coefficient identity `c_r − c_{−r} = d_r` for `n, j ≤ 5`; the gap
closed form for `c_r`; the positivity `d_r > 0`; the truncation identity; and the equality of
the two shapes of the right-hand side.
-/

namespace Principia.MathDB.P334350

open Finset

open Finset

/-- Weakly increasing `j`-tuples with entries in `[1, jn]` -- the write-up's index set. -/
def WI (n j : ℕ) : Finset (Fin j → ℕ) :=
  (Fintype.piFinset fun _ => Finset.Icc 1 (j * n)).filter (fun l => Monotone l)

/-- The left side of the write-up's display (strong). -/
noncomputable def LHS (psi : ℤ → ℂ) (n j : ℕ) : ℂ :=
  ∑ l ∈ WI n j, ∑ i : Fin j, psi ((l i : ℤ) - (i : ℤ) * n)

/-- The right side of the write-up's display (strong). -/
noncomputable def RHS (psi : ℤ → ℂ) (n j : ℕ) : ℂ :=
  ∑ e ∈ Finset.Icc 1 j, ((j * (n + 1)).choose (j - e) : ℂ) *
    ∑ r ∈ Fintype.piFinset (fun _ : Fin e => Finset.Icc 1 n), psi (∑ i, (r i : ℤ))

/-- Marked-tuple count at exponent `r`. -/
def cF (n j : ℕ) (r : ℤ) : ℕ :=
  (((WI n j) ×ˢ (Finset.univ : Finset (Fin j))).filter
    (fun p => ((p.1 p.2 : ℤ) - (p.2 : ℤ) * n) = r)).card

/-- `#{r ∈ [1,n]^e : ∑ r = s}` -- the ordered tuples on the write-up's right-hand side. -/
def Vt (n e : ℕ) (s : ℤ) : ℕ :=
  ((Fintype.piFinset fun _ : Fin e => Finset.Icc 1 n).filter
    (fun r => (∑ i, (r i : ℤ)) = s)).card

/-- The right side's coefficient, in the conjecture's own shape. -/
def dc (n j : ℕ) (s : ℤ) : ℕ :=
  ∑ e ∈ Finset.Icc 1 j, ((j * (n + 1)).choose (j - e)) * Vt n e s

/-- LINK 1 (the whole combinatorial content): the odd part of the marked-tuple
distribution is the coefficient sequence of `R`. -/
def Link1 (n j : ℕ) : Prop :=
  ∀ r : ℤ, 1 ≤ r → (cF n j r : ℤ) - (cF n j (-r) : ℤ) = (dc n j r : ℤ)

/-- LINK 2: the left side is the odd part paired against `psi`. -/
def Link2 (psi : ℤ → ℂ) (n j : ℕ) : Prop :=
  LHS psi n j = ∑ r ∈ Finset.Icc (1 : ℤ) (j * n),
    ((cF n j r : ℂ) - (cF n j (-r) : ℂ)) * psi r

/-- LINK 3: the right side is the coefficient sequence paired against `psi`. -/
def Link3 (psi : ℤ → ℂ) (n j : ℕ) : Prop :=
  RHS psi n j = ∑ r ∈ Finset.Icc (1 : ℤ) (j * n), (dc n j r : ℂ) * psi r

/-- The spine: the three links compose to the write-up's Theorem. -/
theorem main_of_links (psi : ℤ → ℂ) (n j : ℕ)
    (h1 : Link1 n j) (h2 : Link2 psi n j) (h3 : Link3 psi n j) :
    LHS psi n j = RHS psi n j := by
  rw [h2, h3]
  refine Finset.sum_congr rfl fun r hr => ?_
  have hr1 : (1 : ℤ) ≤ r := (Finset.mem_Icc.1 hr).1
  have := h1 r hr1
  have hc : ((cF n j r : ℂ) - (cF n j (-r) : ℂ)) = (dc n j r : ℂ) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℂ)) this
  rw [hc]

/-- Every marked exponent lies in `[1 - (j-1)n, jn]`. -/
lemma expo_maps_to (n j : ℕ) :
    ∀ p ∈ (WI n j) ×ˢ (Finset.univ : Finset (Fin j)),
      ((p.1 p.2 : ℤ) - (p.2 : ℤ) * n) ∈
        Finset.Icc (1 - ((j : ℤ) - 1) * n) ((j : ℤ) * n) := by
  rintro ⟨l, i⟩ hp
  simp only [Finset.mem_product, WI, Finset.mem_filter, Fintype.mem_piFinset] at hp
  obtain ⟨⟨hmem, _⟩, _⟩ := hp
  have h1 := Finset.mem_Icc.1 (hmem i)
  have hlo : (1 : ℤ) ≤ (l i : ℤ) := by exact_mod_cast h1.1
  have hhi : ((l i : ℤ)) ≤ (j : ℤ) * n := by exact_mod_cast h1.2
  have hij : (i : ℤ) ≤ (j : ℤ) - 1 := by
    have : (i : ℕ) < j := i.isLt
    omega
  have hn0 : (0 : ℤ) ≤ (n : ℤ) := Int.natCast_nonneg n
  have hi0 : (0 : ℤ) ≤ (i : ℤ) := Int.natCast_nonneg _
  have hup : (i : ℤ) * n ≤ ((j : ℤ) - 1) * n := by
    exact mul_le_mul_of_nonneg_right hij hn0
  have hdn : (0 : ℤ) ≤ (i : ℤ) * n := mul_nonneg hi0 hn0
  simp only [Finset.mem_Icc]
  constructor <;> linarith

/-- The left side, collected fibrewise by exponent. -/
lemma LHS_eq_sum_cF (psi : ℤ → ℂ) (n j : ℕ) :
    LHS psi n j
      = ∑ y ∈ Finset.Icc (1 - ((j : ℤ) - 1) * n) ((j : ℤ) * n), (cF n j y : ℂ) * psi y := by
  have h := Finset.sum_fiberwise_of_maps_to' (expo_maps_to n j) psi
  rw [LHS, ← Finset.sum_product', ← h]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [cF, Finset.sum_const, nsmul_eq_mul]

/-- `cF` vanishes off the exponent range. -/
lemma cF_eq_zero_of_notMem (n j : ℕ) (y : ℤ)
    (hy : y ∉ Finset.Icc (1 - ((j : ℤ) - 1) * n) ((j : ℤ) * n)) : cF n j y = 0 := by
  rw [cF, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro p hp hpy
  exact hy (hpy ▸ expo_maps_to n j p hp)

/-- Reindex a sum over the negative half by `r ↦ -r`. -/
lemma sum_neg_Icc (f : ℤ → ℂ) (M : ℤ) :
    ∑ y ∈ Finset.Icc (-M) (-1), f y = ∑ r ∈ Finset.Icc (1 : ℤ) M, f (-r) := by
  refine Finset.sum_nbij' (fun y => -y) (fun r => -r) ?_ ?_ ?_ ?_ ?_
  · intro a ha; simp only [Finset.mem_Icc] at ha ⊢; omega
  · intro a ha; simp only [Finset.mem_Icc] at ha ⊢; omega
  · intro a _; simp
  · intro a _; simp
  · intro a _; simp

/-- LINK 2, proved: oddness collapses the exponent distribution to its odd part. -/
theorem link2 (psi : ℤ → ℂ) (n j : ℕ) (hodd : ∀ r : ℤ, psi (-r) = -psi r) :
    Link2 psi n j := by
  have hz : psi 0 = 0 := by
    have h0 := hodd 0
    simp only [neg_zero] at h0
    linear_combination h0 / 2
  have hn0 : (0 : ℤ) ≤ (n : ℤ) := Int.natCast_nonneg n
  have hM0 : (0 : ℤ) ≤ (j : ℤ) * n := by positivity
  have hexp : (1 : ℤ) - ((j : ℤ) - 1) * n = 1 - (j : ℤ) * n + n := by ring
  have hsub : Finset.Icc (1 - ((j : ℤ) - 1) * n) ((j : ℤ) * n)
      ⊆ Finset.Icc (-((j : ℤ) * n)) ((j : ℤ) * n) := by
    intro y hy
    simp only [Finset.mem_Icc] at hy ⊢
    rw [hexp] at hy
    omega
  rw [Link2, LHS_eq_sum_cF]
  rw [Finset.sum_subset hsub (by
    intro y _ hy
    rw [cF_eq_zero_of_notMem n j y hy]
    simp)]
  have hsplit : Finset.Icc (-((j : ℤ) * n)) ((j : ℤ) * n)
      = (Finset.Icc (-((j : ℤ) * n)) (-1) ∪ Finset.Icc (0 : ℤ) 0)
        ∪ Finset.Icc 1 ((j : ℤ) * n) := by
    ext y
    simp only [Finset.mem_union, Finset.mem_Icc]
    omega
  have hd1 : Disjoint (Finset.Icc (-((j : ℤ) * n)) (-1)) (Finset.Icc (0 : ℤ) 0) := by
    rw [Finset.disjoint_left]
    intro y hy hy2
    simp only [Finset.mem_Icc] at hy hy2
    omega
  have hd2 : Disjoint (Finset.Icc (-((j : ℤ) * n)) (-1) ∪ Finset.Icc (0 : ℤ) 0)
      (Finset.Icc 1 ((j : ℤ) * n)) := by
    rw [Finset.disjoint_left]
    intro y hy hy2
    simp only [Finset.mem_union, Finset.mem_Icc] at hy hy2
    omega
  rw [hsplit, Finset.sum_union hd2, Finset.sum_union hd1]
  rw [sum_neg_Icc (fun y => (cF n j y : ℂ) * psi y) ((j : ℤ) * n)]
  simp only [Finset.Icc_self, Finset.sum_singleton, hz, mul_zero, add_zero]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [hodd r]
  ring


/-- Every ordered tuple's sum lies in `[e, e*n]`. -/
lemma tuple_sum_maps_to (n e : ℕ) :
    ∀ r ∈ (Fintype.piFinset fun _ : Fin e => Finset.Icc 1 n),
      (∑ i, (r i : ℤ)) ∈ Finset.Icc (e : ℤ) ((e : ℤ) * n) := by
  intro r hr
  simp only [Fintype.mem_piFinset] at hr
  have hlo : ∀ i : Fin e, (1 : ℤ) ≤ (r i : ℤ) := by
    intro i; exact_mod_cast (Finset.mem_Icc.1 (hr i)).1
  have hhi : ∀ i : Fin e, ((r i : ℤ)) ≤ (n : ℤ) := by
    intro i; exact_mod_cast (Finset.mem_Icc.1 (hr i)).2
  have h1 : ((e : ℤ)) ≤ ∑ i, (r i : ℤ) := by
    calc ((e : ℤ)) = ∑ _i : Fin e, (1 : ℤ) := by simp
    _ ≤ ∑ i, (r i : ℤ) := Finset.sum_le_sum fun i _ => hlo i
  have h2 : (∑ i, (r i : ℤ)) ≤ (e : ℤ) * n := by
    calc (∑ i, (r i : ℤ)) ≤ ∑ _i : Fin e, (n : ℤ) := Finset.sum_le_sum fun i _ => hhi i
    _ = (e : ℤ) * n := by simp [mul_comm]
  exact Finset.mem_Icc.2 ⟨h1, h2⟩

/-- `Vt` vanishes off `[e, e*n]`. -/
lemma Vt_eq_zero_of_notMem (n e : ℕ) (s : ℤ)
    (hs : s ∉ Finset.Icc (e : ℤ) ((e : ℤ) * n)) : Vt n e s = 0 := by
  rw [Vt, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro r hr hrs
  exact hs (hrs ▸ tuple_sum_maps_to n e r hr)

/-- One ordered-tuple sum, collected fibrewise. -/
lemma tuple_sum_collect (psi : ℤ → ℂ) (n e : ℕ) :
    ∑ r ∈ (Fintype.piFinset fun _ : Fin e => Finset.Icc 1 n), psi (∑ i, (r i : ℤ))
      = ∑ s ∈ Finset.Icc (e : ℤ) ((e : ℤ) * n), (Vt n e s : ℂ) * psi s := by
  have h := Finset.sum_fiberwise_of_maps_to' (tuple_sum_maps_to n e) psi
  rw [← h]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Vt, Finset.sum_const, nsmul_eq_mul]

/-- LINK 3, proved: the right side is its coefficient sequence paired against `psi`. -/
theorem link3 (psi : ℤ → ℂ) (n j : ℕ) : Link3 psi n j := by
  have key : ∀ e ∈ Finset.Icc 1 j,
      (∑ r ∈ (Fintype.piFinset fun _ : Fin e => Finset.Icc 1 n), psi (∑ i, (r i : ℤ)))
        = ∑ s ∈ Finset.Icc (1 : ℤ) ((j : ℤ) * n), (Vt n e s : ℂ) * psi s := by
    intro e he
    simp only [Finset.mem_Icc] at he
    rw [tuple_sum_collect]
    refine Finset.sum_subset ?_ ?_
    · intro s hs
      simp only [Finset.mem_Icc] at hs ⊢
      have h1 : (1 : ℤ) ≤ (e : ℤ) := by exact_mod_cast he.1
      have hen : (e : ℤ) * n ≤ (j : ℤ) * n := by
        have : (e : ℤ) ≤ (j : ℤ) := by exact_mod_cast he.2
        exact mul_le_mul_of_nonneg_right this (Int.natCast_nonneg n)
      exact ⟨le_trans h1 hs.1, le_trans hs.2 hen⟩
    · intro s _ hs
      rw [Vt_eq_zero_of_notMem n e s hs]
      simp
  rw [Link3, RHS]
  rw [Finset.sum_congr rfl (fun e he => by rw [key e he])]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [dc]
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun e _ => ?_
  ring

/-- The write-up's Theorem, reduced to ONE obligation: `Link1`, the counting identity.
`Link2` and `Link3` are discharged. -/
theorem main_of_link1 (psi : ℤ → ℂ) (n j : ℕ) (hodd : ∀ r : ℤ, psi (-r) = -psi r)
    (h1 : Link1 n j) :
    LHS psi n j = RHS psi n j :=
  main_of_links psi n j h1 (link2 psi n j hodd) (link3 psi n j)

open Principia.Common.MonotoneTuples in
/-- The marked fibre of `cF`, in closed binomial form.  This is what the promoted
`fiber_binom` feeds. -/
lemma cF_fiber_binom (n j : ℕ) (r : ℤ) (i : Fin j) (v : ℕ)
    (hv : (v : ℤ) = r + (i : ℤ) * n) (h1 : 1 ≤ v) (h2 : v ≤ j * n) :
    #((WI n j).filter (fun l => (l i : ℤ) - (i : ℤ) * n = r))
      = (v + i - 1).choose i * (((j * n) - v) + (j - 1 - i)).choose (j - 1 - i) := by
  have hcongr : (WI n j).filter (fun l => (l i : ℤ) - (i : ℤ) * n = r)
      = (WI n j).filter (fun l => l i = v) := by
    refine Finset.filter_congr ?_
    intro l _
    constructor <;> intro h <;> omega
  rw [hcongr, WI]
  exact fiber_binom (j * n) j i v h1 h2

/-- Off the admissible range the fibre is empty. -/
lemma cF_fiber_zero (n j : ℕ) (r : ℤ) (i : Fin j)
    (h : r + (i : ℤ) * n < 1 ∨ (j : ℤ) * n < r + (i : ℤ) * n) :
    #((WI n j).filter (fun l => (l i : ℤ) - (i : ℤ) * n = r)) = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro l hl hlr
  rw [WI, Finset.mem_filter, Fintype.mem_piFinset] at hl
  have hb := Finset.mem_Icc.1 (hl.1 i)
  have h1 : (1 : ℤ) ≤ (l i : ℤ) := by exact_mod_cast hb.1
  have h2 : ((l i : ℤ)) ≤ (j : ℤ) * n := by exact_mod_cast hb.2
  omega

/-- `cF` is the sum of its marked fibres. -/
lemma cF_eq_sum_fiber (n j : ℕ) (r : ℤ) :
    cF n j r = ∑ i : Fin j, #((WI n j).filter (fun l => (l i : ℤ) - (i : ℤ) * n = r)) := by
  rw [cF]
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun p : (Fin j → ℕ) × Fin j => p.2) (t := (Finset.univ : Finset (Fin j)))
    (fun p _ => Finset.mem_univ p.2)]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.card_bij (fun p _ => p.1) ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨⟨⟨hw, _⟩, hex⟩, hi⟩ := hp
    subst hi
    simp only [Finset.mem_filter]
    exact ⟨hw, hex⟩
  · intro p hp q hq hpq
    simp only [Finset.mem_filter] at hp hq
    have : p.2 = i := hp.2
    have : q.2 = i := hq.2
    exact Prod.ext hpq (by simp_all)
  · intro l hl
    simp only [Finset.mem_filter] at hl
    refine ⟨(l, i), ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨⟨hl.1, Finset.mem_univ i⟩, hl.2⟩, trivial⟩

/-- The reflection `k ↦ j-1-k` on marked indices. -/
def revIdx (j : ℕ) (k : Fin j) : Fin j := ⟨j - 1 - k, by have := k.isLt; omega⟩

@[simp] lemma revIdx_val (j : ℕ) (k : Fin j) : (revIdx j k : ℕ) = j - 1 - k := rfl

lemma revIdx_involutive (j : ℕ) (k : Fin j) : revIdx j (revIdx j k) = k := by
  have := k.isLt
  ext
  simp only [revIdx_val]
  omega

/-- The write-up's involution `λ_i ↦ jn+1-λ_{j-1-i}` on weakly increasing tuples. -/
def reflTuple (n j : ℕ) (l : Fin j → ℕ) : Fin j → ℕ :=
  fun k => j * n + 1 - l (revIdx j k)

lemma reflTuple_mem (n j : ℕ) {l : Fin j → ℕ} (hl : l ∈ WI n j) :
    reflTuple n j l ∈ WI n j := by
  rw [WI, Finset.mem_filter, Fintype.mem_piFinset] at hl ⊢
  obtain ⟨hmem, hmono⟩ := hl
  have hbd : ∀ i : Fin j, 1 ≤ l i ∧ l i ≤ j * n := fun i => Finset.mem_Icc.1 (hmem i)
  refine ⟨?_, ?_⟩
  · intro k
    have := hbd (revIdx j k)
    rw [Finset.mem_Icc]
    unfold reflTuple
    omega
  · intro a b hab
    have hrev : revIdx j b ≤ revIdx j a := by
      have ha := a.isLt
      have hb := b.isLt
      have : (a : ℕ) ≤ (b : ℕ) := hab
      rw [Fin.le_def, revIdx_val, revIdx_val]
      omega
    have h1 := hbd (revIdx j a)
    have h2 := hbd (revIdx j b)
    have := hmono hrev
    unfold reflTuple
    omega

/-- The involution turns the exponent `e` into `n + 1 - e`. -/
lemma reflTuple_expo (n j : ℕ) (l : Fin j → ℕ) (k : Fin j)
    (hb : l (revIdx j k) ≤ j * n) :
    ((reflTuple n j l k : ℤ) - (k : ℤ) * n)
      = ((n : ℤ) + 1) - ((l (revIdx j k) : ℤ) - ((revIdx j k : ℕ) : ℤ) * n) := by
  have hk := k.isLt
  have hcast : ((reflTuple n j l k : ℕ) : ℤ) = (j : ℤ) * n + 1 - (l (revIdx j k) : ℤ) := by
    unfold reflTuple
    have : l (revIdx j k) ≤ j * n + 1 := by omega
    push_cast [Nat.cast_sub this]
    ring
  rw [hcast, revIdx_val]
  have hjk : ((j - 1 - (k : ℕ) : ℕ) : ℤ) = (j : ℤ) - 1 - (k : ℤ) := by
    have : (k : ℕ) ≤ j - 1 := by omega
    push_cast [Nat.cast_sub (by omega : 1 ≤ j), Nat.cast_sub this]
    ring
  rw [hjk]
  ring

/-- **The reflection symmetry of the marked-tuple distribution.**  A bijection, not a
generating-function argument. -/
theorem cF_reflect (n j : ℕ) (e : ℤ) : cF n j e = cF n j ((n : ℤ) + 1 - e) := by
  classical
  rw [cF, cF]
  refine Finset.card_bij
    (fun p _ => (reflTuple n j p.1, revIdx j p.2)) ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product] at hp ⊢
    obtain ⟨⟨hw, _⟩, hex⟩ := hp
    have hbd : ∀ i : Fin j, 1 ≤ p.1 i ∧ p.1 i ≤ j * n := by
      intro i
      rw [WI, Finset.mem_filter, Fintype.mem_piFinset] at hw
      exact Finset.mem_Icc.1 (hw.1 i)
    refine ⟨⟨reflTuple_mem n j hw, Finset.mem_univ _⟩, ?_⟩
    have hrev := revIdx_involutive j p.2
    have hb : p.1 (revIdx j (revIdx j p.2)) ≤ j * n := by
      rw [hrev]; exact (hbd p.2).2
    have := reflTuple_expo n j p.1 (revIdx j p.2) (by rw [hrev]; exact (hbd p.2).2)
    rw [hrev] at this
    rw [this, hex]
  · intro p hp q hq hpq
    have h1 : reflTuple n j p.1 = reflTuple n j q.1 := congrArg Prod.fst hpq
    have h2 : revIdx j p.2 = revIdx j q.2 := congrArg Prod.snd hpq
    simp only [Finset.mem_filter, Finset.mem_product] at hp hq
    have hbp : ∀ i : Fin j, 1 ≤ p.1 i ∧ p.1 i ≤ j * n := by
      intro i
      rw [WI, Finset.mem_filter, Fintype.mem_piFinset] at hp
      exact Finset.mem_Icc.1 (hp.1.1.1 i)
    have hbq : ∀ i : Fin j, 1 ≤ q.1 i ∧ q.1 i ≤ j * n := by
      intro i
      rw [WI, Finset.mem_filter, Fintype.mem_piFinset] at hq
      exact Finset.mem_Icc.1 (hq.1.1.1 i)
    refine Prod.ext ?_ ?_
    · funext k
      have hfk := congrFun h1 (revIdx j k)
      simp only [reflTuple, revIdx_involutive] at hfk
      have hp1 := hbp k
      have hq1 := hbq k
      omega
    · have hv : (revIdx j p.2 : ℕ) = (revIdx j q.2 : ℕ) := by rw [h2]
      simp only [revIdx_val] at hv
      have h3 := p.2.isLt
      have h4 := q.2.isLt
      exact Fin.ext (by omega)
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_product] at hq
    obtain ⟨⟨hw, _⟩, hex⟩ := hq
    have hbd : ∀ i : Fin j, 1 ≤ q.1 i ∧ q.1 i ≤ j * n := by
      intro i
      rw [WI, Finset.mem_filter, Fintype.mem_piFinset] at hw
      exact Finset.mem_Icc.1 (hw.1 i)
    refine ⟨(reflTuple n j q.1, revIdx j q.2), ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_product]
      refine ⟨⟨reflTuple_mem n j hw, Finset.mem_univ _⟩, ?_⟩
      have hrev := revIdx_involutive j q.2
      have := reflTuple_expo n j q.1 (revIdx j q.2) (by rw [hrev]; exact (hbd q.2).2)
      rw [hrev] at this
      rw [this, hex]
      ring
    · refine Prod.ext ?_ (revIdx_involutive j q.2)
      funext k
      have hrev := revIdx_involutive j k
      have hb := hbd k
      simp only [reflTuple, hrev]
      omega

/-- LINK 1b: the SHIFTED form of the counting identity.  Equivalent to `Link1` by the
reflection `cF_reflect`, and it is the form the write-up's generating function produces
(`F(z)(1 - z^{-(n+1)}) = R(z) - R(1/z)`). -/
def Link1b (n j : ℕ) : Prop :=
  ∀ r : ℤ, 1 ≤ r → (cF n j r : ℤ) - (cF n j (r + n + 1) : ℤ) = (dc n j r : ℤ)

/-- `Link1b` implies `Link1`: the negative half of the distribution is the shifted positive
half, by the involution. -/
theorem link1_of_link1b (n j : ℕ) (h : Link1b n j) : Link1 n j := by
  intro r hr
  have hrefl : cF n j (-r) = cF n j (r + n + 1) := by
    have hr' := cF_reflect n j (-r)
    rw [hr']
    congr 1
    ring
  rw [hrefl]
  exact h r hr

/-- The write-up's Theorem, reduced to the SHIFTED counting identity alone. -/
theorem main_of_link1b (psi : ℤ → ℂ) (n j : ℕ) (hodd : ∀ r : ℤ, psi (-r) = -psi r)
    (h : Link1b n j) :
    LHS psi n j = RHS psi n j :=
  main_of_link1 psi n j hodd (link1_of_link1b n j h)

/-- `C(m+u, u)` extended to integer arguments by zero.  At `m = -1` it is the indicator
`[u = 0]`, which is exactly what the endpoint terms of the recursion need. -/
def bin (m u : ℤ) : ℤ := if 0 ≤ u then ((m + u).toNat.choose u.toNat : ℤ) else 0

lemma bin_of_neg {m u : ℤ} (h : u < 0) : bin m u = 0 := by
  simp [bin, not_le.2 h]

lemma bin_zero (m : ℤ) : bin m 0 = 1 := by
  simp [bin]

/-- `bin (-1) v` is the indicator of `v = 0`. -/
lemma bin_neg_one (v : ℤ) : bin (-1) v = if v = 0 then 1 else 0 := by
  rcases lt_trichotomy v 0 with h | h | h
  · rw [bin_of_neg h, if_neg (by omega)]
  · subst h; simp [bin_zero]
  · rw [if_neg (by omega)]
    have hv : v.toNat ≠ 0 := by omega
    have hlt : (-1 + v).toNat < v.toNat := by omega
    simp only [bin, if_pos (le_of_lt h)]
    rw [Nat.choose_eq_zero_of_lt hlt]
    simp

/-- Pascal, in the integer-indexed form the recursion uses. -/
lemma bin_pascal (m u : ℤ) (hm : 0 ≤ m) : bin m u - bin m (u - 1) = bin (m - 1) u := by
  rcases lt_trichotomy u 0 with h | h | h
  · rw [bin_of_neg h, bin_of_neg (by omega), bin_of_neg h]; ring
  · subst h
    rw [bin_zero, bin_of_neg (by norm_num), bin_zero]; ring
  · have hu1 : (0 : ℤ) ≤ u - 1 := by omega
    have hM : 1 ≤ (m + u).toNat := by omega
    obtain ⟨M, hMdef⟩ : ∃ M, (m + u).toNat = M + 1 := ⟨(m + u).toNat - 1, by omega⟩
    obtain ⟨U, hUdef⟩ : ∃ U, u.toNat = U + 1 := ⟨u.toNat - 1, by omega⟩
    have h1 : (m + (u - 1)).toNat = M := by omega
    have h2 : (u - 1).toNat = U := by omega
    have h3 : (m - 1 + u).toNat = M := by omega
    simp only [bin, if_pos (le_of_lt h), if_pos hu1, hMdef, hUdef, h1, h2, h3]
    have := Nat.choose_succ_succ M U
    push_cast [this]
    ring

/-- `φ(k, r)` -- the `z^r`-coefficient at truncation degree `k` of the write-up's
generating function, written as an explicit finite binomial sum. -/
def phi (n j : ℕ) (k r : ℤ) : ℤ :=
  ∑ l ∈ range j, bin (l : ℤ) (r + n * l) * bin ((j : ℤ) - 1 - l) (k - r - n * l)

/-- The per-index summand that both halves of the recursion collapse to. -/
def Sterm (n j : ℕ) (k r : ℤ) (l : ℕ) : ℤ :=
  bin ((l : ℤ) - 1) (r + n * l) * bin ((j : ℤ) - 1 - l) (k - r - n * l)

lemma phi_first (n j : ℕ) (k r : ℤ) :
    phi n j k (r + n) - phi n j (k - 1) (r + n) = ∑ l ∈ range j, Sterm n j k r (l + 1) := by
  rw [phi, phi, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun l hl => ?_
  have hlj : (l : ℤ) < j := by exact_mod_cast Finset.mem_range.1 hl
  have hm : (0 : ℤ) ≤ (j : ℤ) - 1 - l := by omega
  have hp := bin_pascal ((j : ℤ) - 1 - l) (k - (r + n) - n * l) hm
  have he : k - 1 - (r + n) - n * l = (k - (r + n) - n * l) - 1 := by ring
  have hS : Sterm n j k r (l + 1)
      = bin (l : ℤ) (r + (n : ℤ) * l + n)
        * bin ((j : ℤ) - 1 - l - 1) (k - (r + n) - n * l) := by
    unfold Sterm
    congr 1
    · congr 1 <;> push_cast <;> ring
    · congr 1 <;> push_cast <;> ring
  rw [he, hS, show r + (n : ℤ) + (n : ℤ) * l = r + (n : ℤ) * l + n from by ring]
  linear_combination bin (l : ℤ) (r + (n : ℤ) * l + n) * hp

lemma phi_second (n j : ℕ) (k r : ℤ) :
    phi n j k r - phi n j (k - 1) (r - 1) = ∑ l ∈ range j, Sterm n j k r l := by
  rw [phi, phi, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun l hl => ?_
  have hm : (0 : ℤ) ≤ (l : ℤ) := Int.natCast_nonneg l
  have hp := bin_pascal (l : ℤ) (r + n * l) hm
  have he : k - 1 - (r - 1) - n * l = k - r - n * l := by ring
  rw [he, Sterm]
  have hr : r - 1 + n * l = (r + n * l) - 1 := by ring
  rw [hr]
  linear_combination bin ((j : ℤ) - 1 - l) (k - r - n * l) * hp

/-- **The recursion**, replacing the write-up's generating-function step.  Everything is a
finite binomial sum; the proof is Pascal twice, a reindex, and an endpoint telescope. -/
theorem phi_rec (n j : ℕ) (k r : ℤ) :
    phi n j k (r + n) - phi n j k r + phi n j (k - 1) (r - 1) - phi n j (k - 1) (r + n)
      = Sterm n j k r j - Sterm n j k r 0 := by
  have h1 := phi_first n j k r
  have h2 := phi_second n j k r
  have hsum : (∑ l ∈ range j, Sterm n j k r (l + 1))
      = (∑ l ∈ range j, Sterm n j k r l) + Sterm n j k r j - Sterm n j k r 0 := by
    have ha := Finset.sum_range_succ' (Sterm n j k r) j
    have hb := Finset.sum_range_succ (Sterm n j k r) j
    linarith [ha, hb]
  linarith [h1, h2, hsum]

/-- The two endpoint terms, evaluated. -/
lemma Sterm_zero (n j : ℕ) (k r : ℤ) :
    Sterm n j k r 0 = (if r = 0 then bin ((j : ℤ) - 1) (k - r) else 0) := by
  rw [Sterm]
  simp only [Nat.cast_zero, zero_sub, mul_zero, add_zero, sub_zero]
  rw [bin_neg_one]
  split <;> ring

lemma Sterm_top (n j : ℕ) (k r : ℤ) :
    Sterm n j k r j
      = (if k - r - n * j = 0 then bin ((j : ℤ) - 1) (r + n * j) else 0) := by
  rw [Sterm]
  have : ((j : ℤ) - 1 - j) = -1 := by ring
  rw [this, bin_neg_one]
  split <;> ring

/-- `bin` in terms of `Nat.choose`, at nonnegative arguments. -/
lemma bin_eq_choose (m u : ℤ) (hm : 0 ≤ m) (hu : 0 ≤ u) :
    bin m u = ((m.toNat + u.toNat).choose u.toNat : ℤ) := by
  rw [bin, if_pos hu]
  congr 2
  omega

/-- **The bridge**: the marked-tuple count IS the coefficient `φ(jn-1, r-1)`, so the
recursion `phi_rec` applies to `cF`. -/
theorem cF_eq_phi (n j : ℕ) (r : ℤ) :
    (cF n j r : ℤ) = phi n j ((j : ℤ) * n - 1) (r - 1) := by
  rw [cF_eq_sum_fiber, phi]
  push_cast
  rw [← Fin.sum_univ_eq_sum_range (fun l => bin (l : ℤ) (r - 1 + (n : ℤ) * l)
      * bin ((j : ℤ) - 1 - l) ((j : ℤ) * n - 1 - (r - 1) - (n : ℤ) * l)) j]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  have hij : (i : ℕ) < j := i.isLt
  by_cases hlo : 1 ≤ r + (i : ℤ) * n
  · by_cases hhi : r + (i : ℤ) * n ≤ (j : ℤ) * n
    · obtain ⟨v, hvz⟩ : ∃ v : ℕ, (v : ℤ) = r + (i : ℤ) * n :=
        ⟨(r + (i : ℤ) * n).toNat, by omega⟩
      have hjn : ((j * n : ℕ) : ℤ) = (j : ℤ) * n := by push_cast; ring
      -- `omega` treats `n * i` and `i * n` as DIFFERENT atoms; hand it the commutation.
      have hcomm : (n : ℤ) * (i : ℤ) = (i : ℤ) * (n : ℤ) := by ring
      have h1 : 1 ≤ v := by omega
      have h2 : v ≤ j * n := by omega
      rw [cF_fiber_binom n j r i v hvz h1 h2]
      have ev : ((v - 1 : ℕ) : ℤ) = (v : ℤ) - 1 := by
        push_cast [Nat.cast_sub h1]; ring
      have ew : ((j * n - v : ℕ) : ℤ) = ((j * n : ℕ) : ℤ) - v := by
        push_cast [Nat.cast_sub h2]; ring
      have e1 : r - 1 + (n : ℤ) * i = ((v - 1 : ℕ) : ℤ) := by omega
      have e2 : (j : ℤ) * n - 1 - (r - 1) - (n : ℤ) * i = ((j * n - v : ℕ) : ℤ) := by omega
      rw [e1, e2, bin_eq_choose _ _ (Int.natCast_nonneg _) (Int.natCast_nonneg _),
        bin_eq_choose _ _ (by omega) (Int.natCast_nonneg _)]
      simp only [Int.toNat_natCast]
      have hi1 : ((j : ℤ) - 1 - (i : ℤ)).toNat = j - 1 - (i : ℕ) := by omega
      rw [hi1]
      have s1 : (v + (i : ℕ) - 1).choose (i : ℕ) = ((i : ℕ) + (v - 1)).choose (v - 1) := by
        have h : (i : ℕ) + (v - 1) = v + (i : ℕ) - 1 := by omega
        rw [← h]
        exact Nat.choose_symm_add
      have s2 : ((j * n - v) + (j - 1 - (i : ℕ))).choose (j - 1 - (i : ℕ))
          = ((j - 1 - (i : ℕ)) + (j * n - v)).choose (j * n - v) := by
        have h : (j - 1 - (i : ℕ)) + (j * n - v) = (j * n - v) + (j - 1 - (i : ℕ)) := by omega
        rw [h]
        exact Nat.choose_symm_add.symm
      push_cast [s1, s2]
      ring
    · have hcomm : (n : ℤ) * (i : ℤ) = (i : ℤ) * (n : ℤ) := by ring
      rw [cF_fiber_zero n j r i (Or.inr (by omega))]
      have hz : (j : ℤ) * n - 1 - (r - 1) - (n : ℤ) * i < 0 := by omega
      rw [bin_of_neg hz]
      ring
  · have hcomm : (n : ℤ) * (i : ℤ) = (i : ℤ) * (n : ℤ) := by ring
    rw [cF_fiber_zero n j r i (Or.inl (by omega))]
    have hz : r - 1 + (n : ℤ) * i < 0 := by omega
    rw [bin_of_neg hz]
    ring

/-- `φ` vanishes at truncation degree `-1`: in each term one of the two `bin` factors has a
negative argument. -/
lemma phi_neg_one (n j : ℕ) (r : ℤ) : phi n j (-1) r = 0 := by
  rw [phi]
  refine Finset.sum_eq_zero fun l _ => ?_
  rcases lt_or_ge (r + (n : ℤ) * l) 0 with h | h
  · rw [bin_of_neg h, zero_mul]
  · rw [bin_of_neg (by omega : (-1 : ℤ) - r - (n : ℤ) * l < 0), mul_zero]

/-- The endpoint contribution of the recursion at truncation degree `k`. -/
def Eterm (n j : ℕ) (k r : ℤ) : ℤ := Sterm n j k r j - Sterm n j k r 0

/-- **Unrolling the recursion.**  `Bφ_{K-1} = ∑_{k<K} (Cφ_k − E_k)`, where
`B f r = f(r−1) − f(r+n)` and `C f r = f(r−1) − f(r)`.  This is the rearrangement
`B = C − A` applied to `phi_rec`, and it needs no weights at all. -/
theorem Bphi_unroll (n j : ℕ) (r : ℤ) : ∀ K : ℕ,
    phi n j ((K : ℤ) - 1) (r - 1) - phi n j ((K : ℤ) - 1) (r + n)
      = ∑ k ∈ range K, ((phi n j (k : ℤ) (r - 1) - phi n j (k : ℤ) r) - Eterm n j (k : ℤ) r) := by
  intro K
  induction K with
  | zero => simp [phi_neg_one]
  | succ K ih =>
      rw [Finset.sum_range_succ, ← ih]
      have hrec := phi_rec n j (K : ℤ) r
      push_cast
      rw [show (K : ℤ) + 1 - 1 = (K : ℤ) from by ring, Eterm]
      linarith [hrec]

/-- For `r ≥ 1` every endpoint term vanishes, so the unrolled sum is `∑_k Cφ_k`. -/
lemma Eterm_eq_zero (n j : ℕ) (k r : ℤ) (hr : 1 ≤ r) (hk : k < (n : ℤ) * j) :
    Eterm n j k r = 0 := by
  rw [Eterm, Sterm_top, Sterm_zero, if_neg (by omega), if_neg (by omega)]
  ring

/-- LINK 1c: the last obligation, now a single identity between finite binomial sums. -/
def Link1c (n j : ℕ) : Prop :=
  ∀ r : ℤ, 1 ≤ r →
    (∑ k ∈ range (j * n), (phi n j (k : ℤ) (r - 1) - phi n j (k : ℤ) r)) = (dc n j r : ℤ)

theorem link1b_of_link1c (n j : ℕ) (h : Link1c n j) : Link1b n j := by
  intro r hr
  have hcF1 := cF_eq_phi n j r
  have hcF2 := cF_eq_phi n j (r + n + 1)
  have he : (r + (n : ℤ) + 1) - 1 = r + n := by ring
  rw [he] at hcF2
  have hunroll := Bphi_unroll n j r (j * n)
  have hjn : ((j * n : ℕ) : ℤ) - 1 = (j : ℤ) * n - 1 := by push_cast; ring
  rw [hjn] at hunroll
  have hE : (∑ k ∈ range (j * n),
      ((phi n j (k : ℤ) (r - 1) - phi n j (k : ℤ) r) - Eterm n j (k : ℤ) r))
      = ∑ k ∈ range (j * n), (phi n j (k : ℤ) (r - 1) - phi n j (k : ℤ) r) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    have hklt : (k : ℤ) < (n : ℤ) * j := by
      have := Finset.mem_range.1 hk
      have hc : ((j * n : ℕ) : ℤ) = (n : ℤ) * j := by push_cast; ring
      omega
    rw [Eterm_eq_zero n j (k : ℤ) r hr hklt]
    ring
  rw [hE] at hunroll
  rw [hcF1, hcF2, hunroll]
  exact h r hr

/-- The write-up's Theorem, reduced to `Link1c` alone. -/
theorem main_of_link1c (psi : ℤ → ℂ) (n j : ℕ) (hodd : ∀ r : ℤ, psi (-r) = -psi r)
    (h : Link1c n j) :
    LHS psi n j = RHS psi n j :=
  main_of_link1b psi n j hodd (link1b_of_link1c n j h)


/-- Hockey stick for `bin`, shifted: `∑_{k<K} bin m (k - c) = bin (m+1) (K-1-c)`.

`0 ≤ c` is NECESSARY, not decoration: for `c < 0` the sum starts above `u = 0` and the
identity fails (`m = 0, c = -4, K = 0` gives `0 ≠ 4`). -/
theorem bin_sum_range (m : ℤ) (hm : 0 ≤ m) (c : ℤ) (hc : 0 ≤ c) (K : ℕ) :
    ∑ k ∈ Finset.range K, bin m ((k : ℤ) - c) = bin (m + 1) ((K : ℤ) - 1 - c) := by
  induction K with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, Nat.cast_zero]
    exact (bin_of_neg (by omega)).symm
  | succ K ih =>
    rw [Finset.sum_range_succ, ih]
    have hp := bin_pascal (m + 1) ((K : ℤ) - c) (by omega)
    have hm1 : (m + 1) - 1 = m := by ring
    rw [hm1] at hp
    have e1 : ((K : ℤ) - c) - 1 = (K : ℤ) - 1 - c := by ring
    rw [e1] at hp
    have e2 : ((K : ℕ) + 1 : ℤ) - 1 - c = (K : ℤ) - c := by ring
    push_cast
    rw [show ((K : ℤ) + 1) - 1 - c = (K : ℤ) - c from by ring]
    linarith [hp]

/-- The `k`-sum in `Link1c` collapses: every inner sum is a hockey stick. -/
theorem phi_ksum (n j : ℕ) (r : ℤ) (hr : 0 ≤ r) :
    ∑ k ∈ Finset.range (j * n), phi n j (k : ℤ) r
      = ∑ l ∈ Finset.range j,
          bin (l : ℤ) (r + n * l) * bin ((j : ℤ) - l) (((j * n : ℕ) : ℤ) - 1 - r - n * l) := by
  simp only [phi]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l hl => ?_
  have hlj : (l : ℤ) + 1 ≤ (j : ℤ) := by
    have h := Finset.mem_range.mp hl
    exact_mod_cast h
  have hm : (0 : ℤ) ≤ (j : ℤ) - 1 - l := by omega
  have hnl : (0 : ℤ) ≤ (n : ℤ) * (l : ℤ) := by positivity
  have hc : (0 : ℤ) ≤ r + (n : ℤ) * (l : ℤ) := by linarith
  rw [← Finset.mul_sum]
  congr 1
  have h := bin_sum_range ((j : ℤ) - 1 - l) hm (r + (n : ℤ) * (l : ℤ)) hc (j * n)
  calc ∑ k ∈ Finset.range (j * n), bin ((j : ℤ) - 1 - l) ((k : ℤ) - r - (n : ℤ) * (l : ℤ))
      = ∑ k ∈ Finset.range (j * n),
          bin ((j : ℤ) - 1 - l) ((k : ℤ) - (r + (n : ℤ) * (l : ℤ))) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [show (k : ℤ) - r - (n : ℤ) * (l : ℤ) = (k : ℤ) - (r + (n : ℤ) * (l : ℤ))
            from by ring]
    _ = bin (((j : ℤ) - 1 - l) + 1) (((j * n : ℕ) : ℤ) - 1 - (r + (n : ℤ) * (l : ℤ))) := h
    _ = bin ((j : ℤ) - l) (((j * n : ℕ) : ℤ) - 1 - r - (n : ℤ) * (l : ℤ)) := by
        rw [show ((j : ℤ) - 1 - l) + 1 = (j : ℤ) - l from by ring,
          show ((j * n : ℕ) : ℤ) - 1 - (r + (n : ℤ) * (l : ℤ))
            = ((j * n : ℕ) : ℤ) - 1 - r - (n : ℤ) * (l : ℤ) from by ring]

/-- The collapsed sum: `Link1c`'s left side with the `k`-index eliminated. -/
def Gsum (n j : ℕ) (r : ℤ) : ℤ :=
  ∑ l ∈ Finset.range j,
    bin (l : ℤ) (r + n * l) * bin ((j : ℤ) - l) (((j * n : ℕ) : ℤ) - 1 - r - n * l)

/-- The remaining obligation, with no `k`-summation left in it. -/
def Link1d (n j : ℕ) : Prop :=
  ∀ r : ℤ, 1 ≤ r → Gsum n j (r - 1) - Gsum n j r = (dc n j r : ℤ)

/-- `Link1d` suffices for `Link1c`: the `k`-sum was only a hockey stick. -/
theorem link1c_of_link1d (n j : ℕ) (h : Link1d n j) : Link1c n j := by
  intro r hr
  have h1 := phi_ksum n j (r - 1) (by omega)
  have h2 := phi_ksum n j r (by omega)
  rw [Finset.sum_sub_distrib, h1, h2]
  exact h r hr

/-- **The spine, now resting on `Link1d`.**  Same conclusion as `main_of_link1c`, with the
`k`-summation eliminated from the hypothesis. -/
theorem main_of_link1d (psi : ℤ → ℂ) (n j : ℕ) (hodd : ∀ r : ℤ, psi (-r) = -psi r)
    (h : Link1d n j) :
    LHS psi n j = RHS psi n j :=
  main_of_link1c psi n j hodd (link1c_of_link1d n j h)


/-! ### `Link1d` is a FINITE check for each fixed `(n, j)`

The general obligation is what the source proves in `ℚ(z)`.  But both sides vanish past
`r = jn`: every `dc` term counts tuples in `[1,n]^e` with `e ≤ j`, whose sum is at most
`jn`, and every `Gsum` term acquires a negative second `bin` argument.  So `Link1d n j`
reduces to `1 ≤ r ≤ jn`, which is decidable — and each instance makes the spine above
UNCONDITIONAL at that `(n, j)`.
-/

/-- Past `r = jn` every `Gsum` term has a negative second `bin` argument. -/
theorem Gsum_vanish (n j : ℕ) {r : ℤ} (hr : ((j * n : ℕ) : ℤ) ≤ r) :
    Gsum n j r = 0 := by
  rw [Gsum]
  refine Finset.sum_eq_zero fun l hl => ?_
  have hl0 : (0 : ℤ) ≤ (l : ℤ) := Int.natCast_nonneg l
  have hn0 : (0 : ℤ) ≤ (n : ℤ) := Int.natCast_nonneg n
  have hneg : ((j * n : ℕ) : ℤ) - 1 - r - (n : ℤ) * (l : ℤ) < 0 := by nlinarith
  rw [bin_of_neg hneg, mul_zero]

/-- A tuple in `[1,n]^e` sums to at most `e*n`, so `Vt` vanishes beyond that. -/
theorem Vt_vanish (n e : ℕ) {s : ℤ} (hs : ((e * n : ℕ) : ℤ) < s) : Vt n e s = 0 := by
  rw [Vt, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro x hx
  simp only [Fintype.mem_piFinset, Finset.mem_Icc] at hx
  intro hsum
  have hle : (∑ i : Fin e, ((x i : ℕ) : ℤ)) ≤ ((e * n : ℕ) : ℤ) := by
    calc (∑ i : Fin e, ((x i : ℕ) : ℤ)) ≤ ∑ _i : Fin e, ((n : ℕ) : ℤ) := by
          refine Finset.sum_le_sum fun i _ => ?_
          exact_mod_cast (hx i).2
      _ = ((e : ℤ)) * ((n : ℕ) : ℤ) := by
          simp [Finset.sum_const, nsmul_eq_mul]
      _ = ((e * n : ℕ) : ℤ) := by push_cast; ring
  omega

/-- Hence `dc` vanishes past `r = jn`. -/
theorem dc_vanish (n j : ℕ) {r : ℤ} (hr : ((j * n : ℕ) : ℤ) < r) : dc n j r = 0 := by
  rw [dc]
  refine Finset.sum_eq_zero fun e he => ?_
  have hej : e ≤ j := (Finset.mem_Icc.1 he).2
  have hmul : (e * n : ℕ) ≤ (j * n : ℕ) := Nat.mul_le_mul_right n hej
  have hlt : ((e * n : ℕ) : ℤ) < r := by
    have : ((e * n : ℕ) : ℤ) ≤ ((j * n : ℕ) : ℤ) := by exact_mod_cast hmul
    omega
  rw [Vt_vanish n e hlt, mul_zero]

/-- **For fixed `(n, j)`, `Link1d` is exactly the finite range `1 ≤ r ≤ jn`.** -/
theorem link1d_of_range (n j : ℕ)
    (h : ∀ r ∈ Finset.Icc (1 : ℤ) ((j * n : ℕ) : ℤ),
        Gsum n j (r - 1) - Gsum n j r = (dc n j r : ℤ)) :
    Link1d n j := by
  intro r hr
  by_cases hle : r ≤ ((j * n : ℕ) : ℤ)
  · exact h r (Finset.mem_Icc.2 ⟨hr, hle⟩)
  · push_neg at hle
    rw [Gsum_vanish n j (by omega : ((j * n : ℕ) : ℤ) ≤ r - 1),
      Gsum_vanish n j (le_of_lt hle), dc_vanish n j hle]
    simp


/-! ### Unconditional instances

Each `link1d_n_j` discharges the module's one remaining hypothesis by decision, so the
corresponding `main_n_j` is the write-up's Theorem with **no hypothesis carried** — the
first unconditional statements this row produces.  The general `Link1d` is still owed.
-/

/-- `Link1d` at `n = 1`, `j = 1`, by deciding the finite range `1 ≤ r ≤ 1`. -/
theorem link1d_1_1 : Link1d 1 1 := link1d_of_range 1 1 (by decide)

/-- **The write-up's Theorem, unconditionally, at `n = 1`, `j = 1`.** -/
theorem main_1_1 (psi : ℤ → ℂ) (hodd : ∀ r : ℤ, psi (-r) = -psi r) :
    LHS psi 1 1 = RHS psi 1 1 :=
  main_of_link1d psi 1 1 hodd link1d_1_1

/-- `Link1d` at `n = 2`, `j = 2`, by deciding the finite range `1 ≤ r ≤ 4`. -/
theorem link1d_2_2 : Link1d 2 2 := link1d_of_range 2 2 (by decide)

/-- **The write-up's Theorem, unconditionally, at `n = 2`, `j = 2`.** -/
theorem main_2_2 (psi : ℤ → ℂ) (hodd : ∀ r : ℤ, psi (-r) = -psi r) :
    LHS psi 2 2 = RHS psi 2 2 :=
  main_of_link1d psi 2 2 hodd link1d_2_2

/-- `Link1d` at `n = 2`, `j = 3`, by deciding the finite range `1 ≤ r ≤ 6`. -/
theorem link1d_2_3 : Link1d 2 3 := link1d_of_range 2 3 (by decide)

/-- **The write-up's Theorem, unconditionally, at `n = 2`, `j = 3`.** -/
theorem main_2_3 (psi : ℤ → ℂ) (hodd : ∀ r : ℤ, psi (-r) = -psi r) :
    LHS psi 2 3 = RHS psi 2 3 :=
  main_of_link1d psi 2 3 hodd link1d_2_3

/-- `Link1d` at `n = 3`, `j = 2`, by deciding the finite range `1 ≤ r ≤ 6`. -/
theorem link1d_3_2 : Link1d 3 2 := link1d_of_range 3 2 (by decide)

/-- **The write-up's Theorem, unconditionally, at `n = 3`, `j = 2`.** -/
theorem main_3_2 (psi : ℤ → ℂ) (hodd : ∀ r : ℤ, psi (-r) = -psi r) :
    LHS psi 3 2 = RHS psi 3 2 :=
  main_of_link1d psi 3 2 hodd link1d_3_2

/-- `Link1d` at `n = 3`, `j = 3`, by deciding the finite range `1 ≤ r ≤ 9`. -/
theorem link1d_3_3 : Link1d 3 3 := link1d_of_range 3 3 (by decide)

/-- **The write-up's Theorem, unconditionally, at `n = 3`, `j = 3`.** -/
theorem main_3_3 (psi : ℤ → ℂ) (hodd : ∀ r : ℤ, psi (-r) = -psi r) :
    LHS psi 3 3 = RHS psi 3 3 :=
  main_of_link1d psi 3 3 hodd link1d_3_3

/-- `Link1d` at `n = 2`, `j = 4`, by deciding the finite range `1 ≤ r ≤ 8`. -/
theorem link1d_2_4 : Link1d 2 4 := link1d_of_range 2 4 (by decide)

/-- **The write-up's Theorem, unconditionally, at `n = 2`, `j = 4`.** -/
theorem main_2_4 (psi : ℤ → ℂ) (hodd : ∀ r : ℤ, psi (-r) = -psi r) :
    LHS psi 2 4 = RHS psi 2 4 :=
  main_of_link1d psi 2 4 hodd link1d_2_4

/-- `Link1d` at `n = 4`, `j = 2`, by deciding the finite range `1 ≤ r ≤ 8`. -/
theorem link1d_4_2 : Link1d 4 2 := link1d_of_range 4 2 (by decide)

/-- **The write-up's Theorem, unconditionally, at `n = 4`, `j = 2`.** -/
theorem main_4_2 (psi : ℤ → ℂ) (hodd : ∀ r : ℤ, psi (-r) = -psi r) :
    LHS psi 4 2 = RHS psi 4 2 :=
  main_of_link1d psi 4 2 hodd link1d_4_2


/-! ### The uniform family `j = 1`: `Link1d n 1` for EVERY `n`

The point instances above are decided one `(n,j)` at a time.  At `j = 1` the whole family
falls to a closed form, giving infinitely many unconditional instances of the Theorem.
-/

theorem bin_zero_of_nonneg {r : ℤ} (hr : 0 ≤ r) : bin 0 r = 1 := by
  rw [bin, if_pos hr]
  simp

theorem bin_one_of_nonneg {v : ℤ} (hv : 0 ≤ v) : bin 1 v = v + 1 := by
  rw [bin, if_pos hv]
  have h1 : (1 + v).toNat = v.toNat + 1 := by omega
  rw [h1, Nat.choose_succ_self_right]
  omega

/-- `Gsum` at `j = 1` is a single product of two `bin`s. -/
theorem Gsum_j1_raw (n : ℕ) (r : ℤ) :
    Gsum n 1 r = bin 0 r * bin 1 ((n : ℤ) - 1 - r) := by
  rw [Gsum, Finset.sum_range_one]
  norm_num

/-- Closed form of `Gsum` at `j = 1`. -/
theorem Gsum_j1 (n : ℕ) (r : ℤ) :
    Gsum n 1 r = if 0 ≤ r ∧ r ≤ (n : ℤ) - 1 then (n : ℤ) - r else 0 := by
  rw [Gsum_j1_raw]
  by_cases hr : 0 ≤ r
  · rw [bin_zero_of_nonneg hr, one_mul]
    by_cases hv : (0 : ℤ) ≤ (n : ℤ) - 1 - r
    · rw [bin_one_of_nonneg hv, if_pos ⟨hr, by omega⟩]
      ring
    · rw [bin_of_neg (by omega), if_neg (by omega)]
  · rw [bin, if_neg hr, zero_mul, if_neg (by omega)]

/-- `Vt n 1 s` is the indicator of `1 ≤ s ≤ n`. -/
theorem Vt_one (n : ℕ) (s : ℤ) :
    (Vt n 1 s : ℤ) = if 1 ≤ s ∧ s ≤ (n : ℤ) then 1 else 0 := by
  rw [Vt]
  by_cases h : 1 ≤ s ∧ s ≤ (n : ℤ)
  · rw [if_pos h]
    have hset : ((Fintype.piFinset fun _ : Fin 1 => Finset.Icc 1 n).filter
        (fun x => (∑ i, (x i : ℤ)) = s)) = {fun _ => s.toNat} := by
      ext x
      simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc,
        Fin.sum_univ_one, Finset.mem_singleton]
      constructor
      · rintro ⟨hx, hs⟩
        funext i
        have hi : i = 0 := Subsingleton.elim i 0
        subst hi
        omega
      · rintro rfl
        have hs0 : (0 : ℤ) ≤ s := by omega
        have hts : ((s.toNat : ℕ) : ℤ) = s := Int.toNat_of_nonneg hs0
        refine ⟨fun a => ?_, ?_⟩
        · have ha : a = 0 := Subsingleton.elim a 0
          subst ha
          simp only []
          omega
        · simpa using hts
    rw [hset]
    simp
  · rw [if_neg h]
    have hset : ((Fintype.piFinset fun _ : Fin 1 => Finset.Icc 1 n).filter
        (fun x => (∑ i, (x i : ℤ)) = s)) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro x hx
      simp only [Fintype.mem_piFinset, Finset.mem_Icc] at hx
      simp only [Fin.sum_univ_one]
      have := hx 0
      omega
    rw [hset]
    simp

/-- Closed form of `dc` at `j = 1`. -/
theorem dc_j1 (n : ℕ) (r : ℤ) :
    (dc n 1 r : ℤ) = if 1 ≤ r ∧ r ≤ (n : ℤ) then 1 else 0 := by
  rw [dc]
  rw [show Finset.Icc 1 1 = ({1} : Finset ℕ) from rfl, Finset.sum_singleton]
  simp only [Nat.sub_self, Nat.choose_zero_right, one_mul]
  rw [← Vt_one n r]

/-- **`Link1d n 1` for EVERY `n`** — a uniform family, not a decided instance. -/
theorem link1d_j1 (n : ℕ) : Link1d n 1 := by
  intro r hr
  rw [Gsum_j1, Gsum_j1, dc_j1]
  by_cases h1 : r ≤ (n : ℤ)
  · rw [if_pos (show (0 : ℤ) ≤ r - 1 ∧ r - 1 ≤ (n : ℤ) - 1 from ⟨by omega, by omega⟩)]
    rw [if_pos (show 1 ≤ r ∧ r ≤ (n : ℤ) from ⟨hr, h1⟩)]
    by_cases h2 : r ≤ (n : ℤ) - 1
    · rw [if_pos (show (0 : ℤ) ≤ r ∧ r ≤ (n : ℤ) - 1 from ⟨by omega, h2⟩)]
      ring
    · rw [if_neg (show ¬ ((0 : ℤ) ≤ r ∧ r ≤ (n : ℤ) - 1) from by omega)]
      omega
  · rw [if_neg (show ¬ ((0 : ℤ) ≤ r - 1 ∧ r - 1 ≤ (n : ℤ) - 1) from by omega)]
    rw [if_neg (show ¬ ((0 : ℤ) ≤ r ∧ r ≤ (n : ℤ) - 1) from by omega)]
    rw [if_neg (show ¬ (1 ≤ r ∧ r ≤ (n : ℤ)) from by omega)]
    ring

/-- **The write-up's Theorem, unconditionally, for every `n` at `j = 1`.** -/
theorem main_j1 (psi : ℤ → ℂ) (n : ℕ) (hodd : ∀ r : ℤ, psi (-r) = -psi r) :
    LHS psi n 1 = RHS psi n 1 :=
  main_of_link1d psi n 1 hodd (link1d_j1 n)

section FamilyJTwo

/-! ### The uniform family `j = 2`: `Link1d n 2` for EVERY `n`

The source proves only `j = 2`; the write-up generalises to all `j`.  This section closes the
source's own case for every `n`, so the Lean carries everything the source proves,
unconditionally — the general `j` remains the write-up's `φ(z)` step.

**Every indicator below is RELAXED to where its polynomial already vanishes** — the `l = 0` term to
`r ≤ 2n+1` (the product is `0` at `2n` and `2n+1`), the `l = 1` term to `-n-1 ≤ r ≤ n`, `Vt`'s two
pieces to `1 ≤ s` and `s ≤ 2n+1`.  That is not cosmetic: it is what makes the difference identity
hold as a POLYNOMIAL identity on every region but two isolated points, so the whole of
`link1d_j2` is `split_ifs` followed by `ring` or `omega`.
-/

/-- `bin 2 v = (v+1)(v+2)/2`, stated multiplicatively so no division appears. -/
theorem bin_two_of_nonneg {v : ℤ} (hv : 0 ≤ v) : 2 * bin 2 v = (v + 1) * (v + 2) := by
  rw [bin, if_pos hv]
  have hw : (2 + v).toNat = v.toNat + 2 := by omega
  rw [hw]
  have hsymm : (v.toNat + 2).choose v.toNat = (v.toNat + 2).choose 2 := by
    have h := Nat.choose_symm (show 2 ≤ v.toNat + 2 by omega)
    rwa [show v.toNat + 2 - 2 = v.toNat from by omega] at h
  rw [hsymm, Nat.choose_two_right, show v.toNat + 2 - 1 = v.toNat + 1 from by omega]
  have hdvd : 2 ∣ (v.toNat + 2) * (v.toNat + 1) := by
    rw [mul_comm]
    exact (Nat.even_mul_succ_self (v.toNat + 1)).two_dvd
  have hkey : (v.toNat + 2) * (v.toNat + 1) / 2 * 2 = (v.toNat + 2) * (v.toNat + 1) :=
    Nat.div_mul_cancel hdvd
  have hv' : ((v.toNat : ℕ) : ℤ) = v := Int.toNat_of_nonneg hv
  have hcast := congrArg (fun m : ℕ => (m : ℤ)) hkey
  push_cast [hv'] at hcast ⊢
  linarith [hcast]

/-- `Gsum` at `j = 2` is a sum of two products of `bin`s. -/
theorem Gsum_j2_raw (n : ℕ) (r : ℤ) :
    Gsum n 2 r = bin 0 r * bin 2 (2 * (n : ℤ) - 1 - r)
      + bin 1 (r + (n : ℤ)) * bin 1 ((n : ℤ) - 1 - r) := by
  rw [Gsum, Finset.sum_range_succ, Finset.sum_range_one]
  push_cast
  try ring_nf

/-- The `l = 0` term, with the indicator relaxed to `r ≤ 2n+1` — legitimate because the product
vanishes at `r = 2n` and at `r = 2n+1`. -/
theorem Gsum_j2_term1 (n : ℕ) (r : ℤ) :
    2 * (bin 0 r * bin 2 (2 * (n : ℤ) - 1 - r))
      = if 0 ≤ r ∧ r ≤ 2 * (n : ℤ) + 1 then (2 * (n : ℤ) - r) * (2 * (n : ℤ) + 1 - r)
        else 0 := by
  by_cases hr : 0 ≤ r
  · rw [bin_zero_of_nonneg hr, one_mul]
    by_cases h1 : (0 : ℤ) ≤ 2 * (n : ℤ) - 1 - r
    · rw [bin_two_of_nonneg h1, if_pos ⟨hr, by omega⟩]
      ring
    · rw [bin_of_neg (by omega : 2 * (n : ℤ) - 1 - r < 0), mul_zero]
      by_cases h2 : r ≤ 2 * (n : ℤ) + 1
      · rw [if_pos ⟨hr, h2⟩]
        have h3 : r = 2 * (n : ℤ) ∨ r = 2 * (n : ℤ) + 1 := by omega
        rcases h3 with h | h <;> rw [h] <;> ring
      · rw [if_neg (by omega)]
  · rw [bin, if_neg hr, zero_mul, mul_zero, if_neg (by omega)]

/-- The `l = 1` term, with the indicator relaxed to `-n-1 ≤ r ≤ n` — the product vanishes at both
ends. -/
theorem Gsum_j2_term2 (n : ℕ) (r : ℤ) :
    bin 1 (r + (n : ℤ)) * bin 1 ((n : ℤ) - 1 - r)
      = if -(n : ℤ) - 1 ≤ r ∧ r ≤ (n : ℤ) then (r + (n : ℤ) + 1) * ((n : ℤ) - r) else 0 := by
  by_cases h1 : (0 : ℤ) ≤ r + (n : ℤ)
  · by_cases h2 : (0 : ℤ) ≤ (n : ℤ) - 1 - r
    · rw [bin_one_of_nonneg h1, bin_one_of_nonneg h2, if_pos ⟨by omega, by omega⟩]
      ring
    · rw [bin_of_neg (by omega : (n : ℤ) - 1 - r < 0), mul_zero]
      by_cases h3 : r ≤ (n : ℤ)
      · rw [if_pos ⟨by omega, h3⟩, show r = (n : ℤ) from by omega]
        ring
      · rw [if_neg (by omega)]
  · rw [bin_of_neg (by omega : r + (n : ℤ) < 0), zero_mul]
    by_cases h4 : -(n : ℤ) - 1 ≤ r
    · rw [if_pos ⟨h4, by omega⟩, show r = -(n : ℤ) - 1 from by omega]
      ring
    · rw [if_neg (by omega)]

/-- Closed form of `2·Gsum` at `j = 2`. -/
theorem Gsum_j2 (n : ℕ) (r : ℤ) :
    2 * Gsum n 2 r
      = (if 0 ≤ r ∧ r ≤ 2 * (n : ℤ) + 1 then (2 * (n : ℤ) - r) * (2 * (n : ℤ) + 1 - r) else 0)
        + 2 * (if -(n : ℤ) - 1 ≤ r ∧ r ≤ (n : ℤ) then (r + (n : ℤ) + 1) * ((n : ℤ) - r)
          else 0) := by
  rw [Gsum_j2_raw, mul_add, Gsum_j2_term1, Gsum_j2_term2]

/-- The pair count, as a filtered interval: the first coordinate determines the pair. -/
theorem Vt_two_filter (n : ℕ) (s : ℤ) :
    Vt n 2 s = ((Finset.Icc 1 n).filter
      (fun a : ℕ => (1 : ℤ) ≤ s - (a : ℤ) ∧ s - (a : ℤ) ≤ (n : ℤ))).card := by
  have hone : ∀ k : Fin 2, k ≠ 0 → k = 1 := by
    intro k hk
    have h2 := k.isLt
    have h0 : (k : ℕ) ≠ 0 := fun h => hk (Fin.val_injective (by simpa using h))
    exact Fin.val_injective (by simpa using (show (k : ℕ) = 1 by omega))
  rw [Vt]
  refine Finset.card_bij' (fun x _ => x 0)
    (fun a _ => fun k => if k = 0 then a else (s - (a : ℤ)).toNat) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc] at hx ⊢
    obtain ⟨hmem, hsum⟩ := hx
    have h0 := hmem 0
    have h1 := hmem 1
    simp only [Fin.sum_univ_two] at hsum
    exact ⟨h0, by omega, by omega⟩
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_Icc] at ha
    obtain ⟨⟨ha1, ha2⟩, hb1, hb2⟩ := ha
    simp only [Fintype.mem_piFinset, Finset.mem_Icc, Finset.mem_filter, Fin.sum_univ_two]
    refine ⟨fun k => ?_, ?_⟩
    · by_cases hk : k = 0
      · rw [if_pos hk]
        exact ⟨ha1, ha2⟩
      · rw [if_neg hk]
        omega
    · change ((a : ℕ) : ℤ) + (((s - (a : ℤ)).toNat : ℕ) : ℤ) = s
      omega
  · intro x hx
    simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc] at hx
    obtain ⟨hmem, hsum⟩ := hx
    simp only [Fin.sum_univ_two] at hsum
    funext k
    by_cases hk : k = 0
    · rw [if_pos hk, hk]
    · rw [if_neg hk, hone k hk]
      omega
  · intro a _
    simp

/-- Closed form of the pair count, with both indicators relaxed to where the value vanishes. -/
theorem Vt_two (n : ℕ) (s : ℤ) :
    (Vt n 2 s : ℤ)
      = (if 1 ≤ s ∧ s ≤ (n : ℤ) + 1 then s - 1 else 0)
        + (if (n : ℤ) + 1 < s ∧ s ≤ 2 * (n : ℤ) + 1 then 2 * (n : ℤ) + 1 - s else 0) := by
  rw [Vt_two_filter]
  have hset : ((Finset.Icc 1 n).filter
      (fun a : ℕ => (1 : ℤ) ≤ s - (a : ℤ) ∧ s - (a : ℤ) ≤ (n : ℤ)))
      = Finset.Icc (max 1 (s - (n : ℤ)).toNat) (min n (s - 1).toNat) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_Icc, le_min_iff, max_le_iff]
    omega
  rw [hset, Nat.card_Icc]
  split_ifs <;> omega

/-- Closed form of `dc` at `j = 2`. -/
theorem dc_j2 (n : ℕ) (r : ℤ) :
    (dc n 2 r : ℤ)
      = (2 * (n : ℤ) + 2) * (if 1 ≤ r ∧ r ≤ (n : ℤ) then 1 else 0) + (Vt n 2 r : ℤ) := by
  rw [dc]
  rw [show Finset.Icc 1 2 = ({1, 2} : Finset ℕ) from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  push_cast
  rw [Vt_one n r]
  have h1 : ((2 * (n + 1)).choose (2 - 1) : ℤ) = 2 * (n : ℤ) + 2 := by
    rw [show 2 - 1 = 1 from rfl, Nat.choose_one_right]
    push_cast
    ring
  have h2 : ((2 * (n + 1)).choose (2 - 2) : ℤ) = 1 := by
    rw [show 2 - 2 = 0 from rfl, Nat.choose_zero_right]
    norm_num
  rw [h1, h2, one_mul]

/-- **`Link1d n 2` for EVERY `n`** — the source's own case, uniformly.

With the relaxed indicators the difference identity is a polynomial identity on each region; only
`r = n+1` and `r = 2n+2` are isolated points where the branch pins `r`, and `omega` supplies the
pin. -/
theorem link1d_j2 (n : ℕ) : Link1d n 2 := by
  intro r hr
  have key : 2 * (Gsum n 2 (r - 1) - Gsum n 2 r) = 2 * (dc n 2 r : ℤ) := by
    rw [mul_sub, Gsum_j2, Gsum_j2, dc_j2, Vt_two]
    split_ifs <;>
      first
        | omega
        | ring1
        | (obtain rfl : r = (n : ℤ) + 1 := by omega
           ring1)
        | (obtain rfl : r = 2 * (n : ℤ) + 2 := by omega
           ring1)
  linarith [key]

/-- **The write-up's Theorem, unconditionally, for every `n` at `j = 2`** — the case the source
itself proves. -/
theorem main_j2 (psi : ℤ → ℂ) (n : ℕ) (hodd : ∀ r : ℤ, psi (-r) = -psi r) :
    LHS psi n 2 = RHS psi n 2 :=
  main_of_link1d psi n 2 hodd (link1d_j2 n)

end FamilyJTwo

section Convolution

/-! ### `Gsum` is a TRUNCATED convolution, and the untruncated part is Vandermonde

Reindexing by `k = j - l` puts `Gsum` in the shape the residue is really about.  With `m = n + 1`
(so `l + r + n*l = r + m*(j-k)` and `j*n - 1 - r - n*l = m*k - 1 - r`),

    `Gsum n j r = sum_{k=1}^{j} C(r + m*(j-k), j-k) * C(m*k - 1 - r, k)`,

a convolution of two shifted binomial families -- **except that `bin` truncates to zero when its
second argument goes negative, where a generalized binomial coefficient would not.**  That
truncation is the whole of the remaining difficulty, and it is worth stating why.

On `1 <= r <= n` nothing truncates and the identity is VANDERMONDE.  There every composition of
`r` into `e` positive parts automatically has all parts `<= n`, so `Vt n e r = C(r-1, e-1)` and

    `dc n j r = sum_{e=1}^{j} C(j*m, j-e) * C(r-1, e-1) = C(j*m + r - 1, j-1)`

by Vandermonde's convolution.  Past `r = n` BOTH sides acquire inclusion-exclusion corrections --
`Vt` loses the compositions with a part exceeding `n`, `Gsum` loses the terms whose second `bin`
argument goes negative -- and the content of `Link1d` is exactly that those two corrections match.
The write-up does that bookkeeping in `Q(z)`; this module is doing it combinatorially, and this is
where it stands.

`j = 1` and `j = 2` are already unconditional for every `n` (`link1d_j1`, `link1d_j2`), so only
`j >= 3` instances extend coverage.
-/

/-- **`Gsum` reindexed by `k = j - l`**: the `k`-th term pairs `C(r + m(j-k), j-k)` with
`C(mk - 1 - r, k)`, `m = n+1`. -/
theorem Gsum_reindex (n j : ℕ) (r : ℤ) :
    Gsum n j r
      = ∑ k ∈ Finset.Icc 1 j,
          bin ((j : ℤ) - (k : ℤ)) (r + (n : ℤ) * ((j : ℤ) - (k : ℤ)))
            * bin (k : ℤ) ((n : ℤ) * (k : ℤ) - 1 - r) := by
  rw [Gsum]
  refine Finset.sum_nbij' (fun l => j - l) (fun k => j - k) ?_ ?_ ?_ ?_ ?_
  · intro l hl
    simp only [Finset.mem_range] at hl
    simp only [Finset.mem_Icc]
    omega
  · intro k hk
    simp only [Finset.mem_Icc] at hk
    simp only [Finset.mem_range]
    omega
  · intro l hl
    simp only [Finset.mem_range] at hl
    omega
  · intro k hk
    simp only [Finset.mem_Icc] at hk
    omega
  · intro l hl
    simp only [Finset.mem_range] at hl
    have hc : ((j - l : ℕ) : ℤ) = (j : ℤ) - (l : ℤ) := by omega
    have e3 : (j : ℤ) - ((j : ℤ) - (l : ℤ)) = (l : ℤ) := by ring
    have e2 : (n : ℤ) * ((j : ℤ) - (l : ℤ)) - 1 - r
        = ((j * n : ℕ) : ℤ) - 1 - r - (n : ℤ) * (l : ℤ) := by push_cast; ring
    rw [hc, e3, e2]

end Convolution

section MoreInstances

/-! ### More decided instances at `j >= 3`

`link1d_of_range` turns `Link1d n j` into a finite check on `1 <= r <= jn`, so each pair is
decidable.  `j = 1, 2` are already covered for every `n`, so only `j >= 3` adds anything.
-/

theorem link1d_4_3 : Link1d 4 3 := link1d_of_range 4 3 (by decide)

theorem main_4_3 (psi : ℤ → ℂ) (hodd : ∀ r : ℤ, psi (-r) = -psi r) :
    LHS psi 4 3 = RHS psi 4 3 :=
  main_of_link1d psi 4 3 hodd link1d_4_3

theorem link1d_3_4 : Link1d 3 4 := link1d_of_range 3 4 (by decide)

theorem main_3_4 (psi : ℤ → ℂ) (hodd : ∀ r : ℤ, psi (-r) = -psi r) :
    LHS psi 3 4 = RHS psi 3 4 :=
  main_of_link1d psi 3 4 hodd link1d_3_4

theorem link1d_2_5 : Link1d 2 5 := link1d_of_range 2 5 (by decide)

theorem main_2_5 (psi : ℤ → ℂ) (hodd : ∀ r : ℤ, psi (-r) = -psi r) :
    LHS psi 2 5 = RHS psi 2 5 :=
  main_of_link1d psi 2 5 hodd link1d_2_5

end MoreInstances

section GsumLow

open Principia.Common

/-! ### `Gsum` in closed form where nothing truncates

`Principia.Common.RotheConvolution` proves that `F_j(x,y) = ∑_{k≤j} C(x+m(j−k), j−k)·C(y+mk, k)`
depends only on `x+y`, for the GENERALIZED binomial `Ring.choose`.  This section spends it.

`bin` agrees with `Ring.choose` exactly when both of its arguments are nonnegative
(`bin_eq_ringChoose`), and in `Gsum`'s reindexed form the second factor is
`bin k (n·k − 1 − r)`, whose second argument is `≥ n − 1 − r`.  **So on `0 ≤ r ≤ n − 1` no term
truncates**, `Gsum` is the `k ≥ 1` part of `F_j(r, −1−r)`, and the missing `k = 0` term is
`C(r + m·j, j)`.  Since `r + (−1−r) = −1` regardless of `r`, the convolution is a CONSTANT, so

    `Gsum n j r = F_j(0,−1) − C(r + m·j, j)`     for `0 ≤ r ≤ n − 1`,

and differencing that in `r` is one more instance of Pascal:

    `Gsum n j (r−1) − Gsum n j r = C(r − 1 + m·j, j − 1)`     for `1 ≤ r ≤ n − 1`.

**This is one of the two halves of `Link1d` on the untruncated range.**  The other half is that
`dc n j r` equals the same binomial there, which is Vandermonde applied to
`Vt n e r = C(r−1, e−1)` — true because a composition of `r ≤ n` into positive parts has every
part `≤ n` automatically.  Neither half is the truncated region, which remains the residue.
-/

/-- `bin` IS the generalized binomial when both arguments are nonnegative. -/
theorem bin_eq_ringChoose {M U : ℤ} (hM : 0 ≤ M) (hU : 0 ≤ U) :
    bin M U = Ring.choose (M + U) M.toNat := by
  have hsum : (0 : ℤ) ≤ M + U := by linarith
  have hcast : (((M + U).toNat : ℕ) : ℤ) = M + U := Int.toNat_of_nonneg hsum
  have key : Ring.choose (M + U) M.toNat = (((M + U).toNat.choose M.toNat : ℕ) : ℤ) := by
    conv_lhs => rw [← hcast]
    exact Ring.choose_natCast _ _
  rw [bin, if_pos hU, key]
  congr 1
  have hle : M.toNat ≤ (M + U).toNat := by omega
  have hsym := Nat.choose_symm hle
  rw [show (M + U).toNat - M.toNat = U.toNat from by omega] at hsym
  exact hsym

/-- On `0 ≤ r ≤ n − 1` the `k`-th term of `Gsum`'s reindexed form is the `k`-th term of the
generalized convolution at `(r, −1−r)`. -/
theorem Gsum_term_eq {n j : ℕ} {r : ℤ} (h0 : 0 ≤ r) (h1 : r ≤ (n : ℤ))
    {k : ℕ} (hk1 : 1 ≤ k) (hkj : k ≤ j) :
    bin ((j : ℤ) - (k : ℤ)) (r + (n : ℤ) * ((j : ℤ) - (k : ℤ)))
        * bin (k : ℤ) ((n : ℤ) * (k : ℤ) - 1 - r)
      = rothe ((n : ℤ) + 1) (j - k) r * rothe ((n : ℤ) + 1) k (-1 - r) := by
  have hn0 : (0 : ℤ) ≤ (n : ℤ) := Int.natCast_nonneg n
  have hjk : ((j - k : ℕ) : ℤ) = (j : ℤ) - (k : ℤ) := by omega
  have hk0 : (0 : ℤ) ≤ (k : ℤ) := Int.natCast_nonneg k
  have hM1 : (0 : ℤ) ≤ (j : ℤ) - (k : ℤ) := by omega
  have hU1 : (0 : ℤ) ≤ r + (n : ℤ) * ((j : ℤ) - (k : ℤ)) := by positivity
  have hkZ : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk1
  have hnk : (n : ℤ) ≤ (n : ℤ) * (k : ℤ) := by nlinarith
  by_cases hU2 : (0 : ℤ) ≤ (n : ℤ) * (k : ℤ) - 1 - r
  · rw [bin_eq_ringChoose hM1 hU1, bin_eq_ringChoose hk0 hU2]
    simp only [rothe]
    congr 1 <;> congr 1 <;>
      first
        | (rw [hjk]; ring1)
        | ring1
        | omega
  · -- the boundary term: `bin` truncates, and the generalized factor vanishes there too,
    -- because its upper index sits strictly below its lower one
    have hneg : (n : ℤ) * (k : ℤ) - 1 - r < 0 := by omega
    have he : (-1 - r) + ((n : ℤ) + 1) * (k : ℤ)
        = ((n : ℤ) * (k : ℤ) - 1 - r) + (k : ℤ) := by ring
    have hz : rothe ((n : ℤ) + 1) k (-1 - r) = 0 := by
      refine ringChoose_eq_zero_of_lt ?_ ?_
      · rw [he]; linarith
      · rw [he]; linarith
    rw [bin_of_neg hneg, mul_zero, hz, mul_zero]

/-- **`Gsum` in closed form on the untruncated range.** -/
theorem Gsum_low (n j : ℕ) {r : ℤ} (h0 : 0 ≤ r) (h1 : r ≤ (n : ℤ)) :
    Gsum n j r
      = rotheConv ((n : ℤ) + 1) j 0 (-1) - Ring.choose (r + ((n : ℤ) + 1) * (j : ℤ)) j := by
  classical
  have hconv : rotheConv ((n : ℤ) + 1) j r (-1 - r) = rotheConv ((n : ℤ) + 1) j 0 (-1) :=
    rotheConv_eq_of_add_eq _ j r (-1 - r) 0 (-1) (by ring)
  have hins : Finset.range (j + 1) = insert 0 (Finset.Icc 1 j) := by
    ext k
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  have hsplit : rotheConv ((n : ℤ) + 1) j r (-1 - r)
      = rothe ((n : ℤ) + 1) j r * rothe ((n : ℤ) + 1) 0 (-1 - r)
        + ∑ k ∈ Finset.Icc 1 j,
            rothe ((n : ℤ) + 1) (j - k) r * rothe ((n : ℤ) + 1) k (-1 - r) := by
    rw [rotheConv, hins, Finset.sum_insert (by simp)]
    simp
  have hzero : rothe ((n : ℤ) + 1) j r * rothe ((n : ℤ) + 1) 0 (-1 - r)
      = Ring.choose (r + ((n : ℤ) + 1) * (j : ℤ)) j := by
    simp [rothe]
  rw [Gsum_reindex]
  have hterms : ∑ k ∈ Finset.Icc 1 j,
      bin ((j : ℤ) - (k : ℤ)) (r + (n : ℤ) * ((j : ℤ) - (k : ℤ)))
        * bin (k : ℤ) ((n : ℤ) * (k : ℤ) - 1 - r)
      = ∑ k ∈ Finset.Icc 1 j,
          rothe ((n : ℤ) + 1) (j - k) r * rothe ((n : ℤ) + 1) k (-1 - r) := by
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hk' := Finset.mem_Icc.mp hk
    exact Gsum_term_eq h0 h1 hk'.1 hk'.2
  rw [hterms]
  rw [hzero] at hsplit
  rw [hconv] at hsplit
  linarith [hsplit]

/-- **The `Gsum` side of `Link1d`, on the untruncated range.**  One more instance of Pascal.

Stated at `j + 1` rather than at `j` with `j - 1`: at `j = 0` both `Gsum`s are empty sums, so the
left side is `0`, while `Ring.choose _ (0 - 1)` truncates to `Ring.choose _ 0 = 1`.  The
natural-subtraction form is FALSE there, and writing `j + 1` removes the trap rather than guarding
against it. -/
theorem Gsum_diff_low (n j : ℕ) {r : ℤ} (h1 : 1 ≤ r) (h2 : r ≤ (n : ℤ)) :
    Gsum n (j + 1) (r - 1) - Gsum n (j + 1) r
      = Ring.choose (r - 1 + ((n : ℤ) + 1) * ((j + 1 : ℕ) : ℤ)) j := by
  rw [Gsum_low n (j + 1) (r := r - 1) (by omega) (by omega),
    Gsum_low n (j + 1) (r := r) (by omega) (by omega)]
  have hp := Ring.choose_succ_succ (r - 1 + ((n : ℤ) + 1) * ((j + 1 : ℕ) : ℤ)) j
  have e1 : r - 1 + ((n : ℤ) + 1) * ((j + 1 : ℕ) : ℤ) + 1
      = r + ((n : ℤ) + 1) * ((j + 1 : ℕ) : ℤ) := by ring
  rw [e1] at hp
  linarith [hp]

end GsumLow

section DcLow

open Principia.Common

/-! ### The `dc` side on the untruncated range

`Gsum_diff_low` computed the `Gsum` side of `Link1d` for `1 ≤ r ≤ n − 1`.  This is the other side
there, and it is Vandermonde: `dc n (j+1) r = ∑_{e=1}^{j+1} C((j+1)(n+1), j+1−e)·Vt n e r`, and on
the low range `Vt n e r` is the number of compositions of `r` into `e` positive parts — the upper
bound `n` being vacuous, since a composition of `r ≤ n` into positive parts has every part `≤ r`.

**The composition count is the one thing not yet formalised**, so it enters here as an explicit
hypothesis rather than as a carried `Prop`: `hVt` is a statement about `Vt` alone, decidable for
each instance, and Mathlib can supply it —
`Finset.card_finsuppAntidiag_nat_eq_choose` gives `#(s.finsuppAntidiag m) = (#s + m − 1).choose m`,
which at `#s = e` and `m = r − e` is `(r−1).choose (r−e) = (r−1).choose (e−1)`.  What is missing is
only the bridge from `Vt`'s filtered `Fintype.piFinset` to `finsuppAntidiag`, through the shift
`y = x − 1` that turns positive parts into arbitrary ones.
-/

/-- **The `dc` side of `Link1d`, given the composition count.**

**It needs no range hypothesis.**  The statement was first written with `1 <= r` and `r <= n`
carried alongside `hVt`, and the linter reported both unused -- correctly: the reindex and
Vandermonde are valid for every `r`.  The low range is what makes `hVt` TRUE, not what makes this
implication valid, so it belongs there and nowhere else. -/
theorem dc_low (n j r : ℕ)
    (hVt : ∀ i : ℕ, i ≤ j → Vt n (i + 1) (r : ℤ) = (r - 1).choose i) :
    dc n (j + 1) (r : ℤ) = ((j + 1) * (n + 1) + (r - 1)).choose j := by
  classical
  have hreindex : dc n (j + 1) (r : ℤ)
      = ∑ i ∈ Finset.range (j + 1),
          ((j + 1) * (n + 1)).choose (j - i) * Vt n (i + 1) (r : ℤ) := by
    rw [dc]
    refine Finset.sum_nbij' (fun e => e - 1) (fun i => i + 1) ?_ ?_ ?_ ?_ ?_
    · intro e he
      simp only [Finset.mem_Icc] at he
      simp only [Finset.mem_range]
      omega
    · intro i hi
      simp only [Finset.mem_range] at hi
      simp only [Finset.mem_Icc]
      omega
    · intro e he
      simp only [Finset.mem_Icc] at he
      omega
    · intro i _
      omega
    · intro e he
      simp only [Finset.mem_Icc] at he
      have hidx : j + 1 - e = j - (e - 1) := by omega
      have hsucc : e - 1 + 1 = e := by omega
      rw [hidx, hsucc]
  rw [hreindex]
  have hterms : ∀ i ∈ Finset.range (j + 1),
      ((j + 1) * (n + 1)).choose (j - i) * Vt n (i + 1) (r : ℤ)
        = ((j + 1) * (n + 1)).choose (j - i) * (r - 1).choose i := by
    intro i hi
    have hij : i ≤ j := by
      simp only [Finset.mem_range] at hi
      omega
    rw [hVt i hij]
  rw [Finset.sum_congr rfl hterms]
  exact vandermonde_range ((j + 1) * (n + 1)) (r - 1) j

end DcLow

section VtLow

open Principia.Common

/-! ### The composition count

`dc_low` takes `Vt n e r = C(r−1, e−1)` as a hypothesis.  This discharges it for `1 ≤ r ≤ n`.

**Mathlib has the count, for `Finsupp`s.**  `Finset.card_finsuppAntidiag_nat_eq_choose` gives
`#(s.finsuppAntidiag m) = (#s + m − 1).choose m`.  And `finsuppAntidiag` is DEFINED as a `map` of
an `attach` of `Finset.piAntidiag`, so the two have the same cardinality — which turns the count
into a statement about PLAIN FUNCTIONS (`card_piAntidiag_nat`), where `Vt` lives.

The rest is the shift `y = x − 1` carrying positive parts to arbitrary ones, and two degenerate
cases that must be excluded rather than proved: at `r = 0` the claim fails for `e = 1`
(`Vt n 1 0 = 0` but `(0−1).choose 0 = 1` under natural subtraction), and for `e > r` both sides
are `0` but no bijection exists, so that case is handled separately.
-/

/-- `Vt`'s defining condition, with the sum taken in `ℕ`. -/
theorem Vt_natSum (n e s : ℕ) :
    Vt n e (s : ℤ)
      = ((Fintype.piFinset fun _ : Fin e => Finset.Icc 1 n).filter
          (fun x => ∑ k, x k = s)).card := by
  classical
  rw [Vt]
  congr 1
  ext x
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hx, h⟩
    exact ⟨hx, by exact_mod_cast h⟩
  · rintro ⟨hx, h⟩
    exact ⟨hx, by exact_mod_cast h⟩

/-- **The composition count on the untruncated range.** -/
theorem Vt_low (n r : ℕ) (hr : 1 ≤ r) (hrn : r ≤ n) (i : ℕ) :
    Vt n (i + 1) (r : ℤ) = (r - 1).choose i := by
  classical
  rw [Vt_natSum]
  by_cases hir : r < i + 1
  · -- too many parts: both sides vanish
    have hempty : ((Fintype.piFinset fun _ : Fin (i + 1) => Finset.Icc 1 n).filter
        (fun x => ∑ k, x k = r)) = ∅ := by
      ext x
      simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc,
        Finset.notMem_empty, iff_false, not_and]
      intro hx hsum
      have hge : (i + 1) ≤ ∑ k : Fin (i + 1), x k := by
        calc (i + 1) = ∑ _k : Fin (i + 1), 1 := by simp
          _ ≤ ∑ k : Fin (i + 1), x k := Finset.sum_le_sum (fun k _ => (hx k).1)
      omega
    rw [hempty, Finset.card_empty]
    exact (Nat.choose_eq_zero_of_lt (by omega)).symm
  · -- the shift `y = x - 1`
    have hir : i + 1 ≤ r := not_lt.mp hir
    have hbij : ((Fintype.piFinset fun _ : Fin (i + 1) => Finset.Icc 1 n).filter
        (fun x => ∑ k, x k = r)).card
        = (Finset.piAntidiag (Finset.univ : Finset (Fin (i + 1))) (r - (i + 1))).card := by
      refine Finset.card_bij' (fun x _ => fun k => x k - 1) (fun y _ => fun k => y k + 1)
        ?_ ?_ ?_ ?_
      · intro x hx
        simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc] at hx
        simp only [Finset.mem_piAntidiag, ne_eq, Finset.mem_univ, implies_true, and_true]
        have hback : ∑ k : Fin (i + 1), ((x k - 1) + 1) = ∑ k : Fin (i + 1), x k :=
          Finset.sum_congr rfl (fun k _ => by have := (hx.1 k).1; omega)
        have hsplit : ∑ k : Fin (i + 1), ((x k - 1) + 1)
            = (∑ k : Fin (i + 1), (x k - 1)) + (i + 1) := by
          rw [Finset.sum_add_distrib]
          simp
        omega
      · intro y hy
        simp only [Finset.mem_piAntidiag] at hy
        simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc]
        have hsum : ∑ k : Fin (i + 1), (y k + 1) = (∑ k : Fin (i + 1), y k) + (i + 1) := by
          rw [Finset.sum_add_distrib]
          simp
        have hy1 : ∑ k : Fin (i + 1), y k = r - (i + 1) := hy.1
        refine ⟨fun k => ⟨by omega, ?_⟩, by omega⟩
        have hle : y k ≤ ∑ k : Fin (i + 1), y k :=
          Finset.single_le_sum (f := fun k : Fin (i + 1) => y k)
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
        omega
      · intro x hx
        simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc] at hx
        funext k
        show x k - 1 + 1 = x k
        have := (hx.1 k).1
        omega
      · intro y _
        funext k
        show y k + 1 - 1 = y k
        omega
    rw [hbij, card_piAntidiag_nat]
    simp only [Finset.card_univ, Fintype.card_fin]
    have h1 : i + 1 + (r - (i + 1)) - 1 = r - 1 := by omega
    rw [h1]
    have h2 : r - 1 - (r - (i + 1)) = i := by omega
    rw [← Nat.choose_symm (by omega : r - (i + 1) ≤ r - 1), h2]


/-- **`Link1d` on the untruncated range, unconditionally.**  `Gsum_diff_low` and `dc_low` both
land on the same binomial, and `Vt_low` discharges the count `dc_low` was carrying. -/
theorem link1d_low (n j r : ℕ) (hr : 1 ≤ r) (hrn : r ≤ n) :
    Gsum n (j + 1) ((r : ℤ) - 1) - Gsum n (j + 1) (r : ℤ) = (dc n (j + 1) (r : ℤ) : ℤ) := by
  have hz1 : (1 : ℤ) ≤ (r : ℤ) := by exact_mod_cast hr
  have hz2 : (r : ℤ) ≤ (n : ℤ) := by exact_mod_cast hrn
  rw [Gsum_diff_low n j hz1 hz2, dc_low n j r (fun i _ => Vt_low n r hr (by omega) i)]
  have harg : (r : ℤ) - 1 + ((n : ℤ) + 1) * ((j + 1 : ℕ) : ℤ)
      = (((j + 1) * (n + 1) + (r - 1) : ℕ) : ℤ) := by
    push_cast [Nat.cast_sub hr]
    ring
  rw [harg, Ring.choose_natCast]

end VtLow

/-! ### Inclusion–exclusion for `Vt`: the last mathematical ingredient of `Link1d`

`Vt n e s` counts the `e`-tuples in `[1,n]` summing to `s`.  The module has closed forms for
`e = 1, 2` (`Vt_one`, `Vt_two`) and on the untruncated range (`Vt_low`); the general `e` is what
`Link1d`'s `dc`-side correction needs, and it is proved here by **induction on the number of
parts**, not by a sieve over the coordinates that exceed `n`.  The induction needs only

* `Vt_recursion` — fibre the tuples over the first coordinate's value;
* `Principia.Common.ibin_telescope` — the sum over that value telescopes;
* `Principia.Common.alt_binom_diff_sum` — Pascal reassembles the coefficients.

**The coefficient must be the truncating `ibin`, not `Ring.choose`**: with the generalized
binomial the formula is false (`probe_334350_vt.py` measures 120 mismatches, every one at a
negative argument).  Both spellings typecheck, so the negative control is the only thing that
separates them.
-/

section VtInclExcl

open Principia.Common

/-- **The recursion on the number of parts.**  Fibre the tuples over the value of the first
coordinate; `Fin.cons`/`Fin.tail` is the bijection and `Fin.sum_univ_succ` splits the sum. -/
theorem Vt_recursion (n e : ℕ) (s : ℤ) :
    Vt n (e + 1) s = ∑ a ∈ Finset.Icc 1 n, Vt n e (s - (a : ℤ)) := by
  classical
  have H : ∀ x ∈ (Fintype.piFinset fun _ : Fin (e + 1) => Finset.Icc 1 n).filter
      (fun x => (∑ i, (x i : ℤ)) = s), x 0 ∈ Finset.Icc 1 n := by
    intro x hx
    simp only [Finset.mem_filter, Fintype.mem_piFinset] at hx
    exact hx.1 0
  rw [Vt, Finset.card_eq_sum_card_fiberwise H]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [Vt]
  refine Finset.card_bij' (fun x _ => fun i : Fin e => x i.succ)
    (fun y _ => Fin.cons a y) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Fintype.mem_piFinset] at hx ⊢
    obtain ⟨⟨hmem, hsum⟩, h0⟩ := hx
    have hsplit : (∑ i : Fin (e + 1), ((x i : ℕ) : ℤ))
        = ((x 0 : ℕ) : ℤ) + ∑ i : Fin e, ((x i.succ : ℕ) : ℤ) :=
      Fin.sum_univ_succ (fun i => ((x i : ℕ) : ℤ))
    refine ⟨fun i => hmem i.succ, ?_⟩
    rw [h0] at hsplit
    omega
  · intro y hy
    simp only [Finset.mem_filter, Fintype.mem_piFinset] at hy ⊢
    obtain ⟨hmem, hsum⟩ := hy
    have hsplit : (∑ i : Fin (e + 1), (((Fin.cons a y : Fin (e + 1) → ℕ) i : ℕ) : ℤ))
        = (((Fin.cons a y : Fin (e + 1) → ℕ) 0 : ℕ) : ℤ)
          + ∑ i : Fin e, (((Fin.cons a y : Fin (e + 1) → ℕ) i.succ : ℕ) : ℤ) :=
      Fin.sum_univ_succ _
    simp only [Fin.cons_zero, Fin.cons_succ] at hsplit
    refine ⟨⟨fun k => ?_, ?_⟩, ?_⟩
    · refine Fin.cases ?_ ?_ k
      · simpa using ha
      · intro i
        simpa using hmem i
    · omega
    · simp
  · intro x hx
    simp only [Finset.mem_filter] at hx
    have h0 : x 0 = a := hx.2
    rw [← h0]
    exact Fin.cons_self_tail x
  · intro y _
    funext i
    simp

/-- **Inclusion–exclusion for compositions with bounded parts.**
`Vt n (e+1) s = ∑_i (-1)^i C(e+1, i) · ibin (s - 1 - n·i) e`. -/
theorem Vt_inclExcl (n : ℕ) : ∀ (e : ℕ) (s : ℤ),
    (Vt n (e + 1) s : ℤ)
      = ∑ i ∈ Finset.range (e + 2), (-1 : ℤ) ^ i * ((e + 1).choose i : ℤ)
          * ibin (s - 1 - (n : ℤ) * (i : ℤ)) e := by
  intro e
  induction e with
  | zero =>
      intro s
      have e0 : ∀ z : ℤ, ibin z 0 = if 0 ≤ z then 1 else 0 := by
        intro z
        unfold ibin
        split <;> simp
      simp only [Nat.zero_add]
      rw [Vt_one, Finset.sum_range_succ, Finset.sum_range_one, e0, e0]
      norm_num
      split_ifs <;> omega
  | succ e ih =>
      intro s
      have hrec : (Vt n (e + 2) s : ℤ)
          = ∑ a ∈ Finset.Icc 1 n, (Vt n (e + 1) (s - (a : ℤ)) : ℤ) := by
        rw [Vt_recursion]
        push_cast
        rfl
      rw [hrec]
      have hstep : ∀ a ∈ Finset.Icc 1 n, (Vt n (e + 1) (s - (a : ℤ)) : ℤ)
          = ∑ i ∈ Finset.range (e + 2), (-1 : ℤ) ^ i * ((e + 1).choose i : ℤ)
              * ibin (s - (a : ℤ) - 1 - (n : ℤ) * (i : ℤ)) e :=
        fun a _ => ih (s - (a : ℤ))
      rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
      have hinner : ∀ i ∈ Finset.range (e + 2),
          (∑ a ∈ Finset.Icc 1 n, (-1 : ℤ) ^ i * ((e + 1).choose i : ℤ)
              * ibin (s - (a : ℤ) - 1 - (n : ℤ) * (i : ℤ)) e)
            = (-1 : ℤ) ^ i * ((e + 1).choose i : ℤ)
                * (ibin (s - 1 - (n : ℤ) * (i : ℤ)) (e + 1)
                    - ibin (s - 1 - (n : ℤ) * ((i : ℤ) + 1)) (e + 1)) := by
        intro i _
        rw [← Finset.mul_sum]
        congr 1
        have harg : ∀ a : ℕ, s - (a : ℤ) - 1 - (n : ℤ) * (i : ℤ)
            = s - 1 - (n : ℤ) * (i : ℤ) - (a : ℤ) := by
          intro a
          ring
        rw [Finset.sum_congr rfl (fun a _ => by rw [harg a]), ibin_telescope]
        have hz : s - 1 - (n : ℤ) * (i : ℤ) - (n : ℤ)
            = s - 1 - (n : ℤ) * ((i : ℤ) + 1) := by ring
        rw [hz]
      rw [Finset.sum_congr rfl hinner]
      have hu : ∀ i : ℕ, s - 1 - (n : ℤ) * ((i : ℤ) + 1)
          = s - 1 - (n : ℤ) * ((i + 1 : ℕ) : ℤ) := by
        intro i
        push_cast
        ring
      rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.range (e + 2)) => by rw [hu i])]
      exact alt_binom_diff_sum (fun i => ibin (s - 1 - (n : ℤ) * (i : ℤ)) (e + 1)) (e + 1)

end VtInclExcl

/-! ### `Gsum` off the untruncated range: the correction, named

`Gsum_low` holds only for `r ≤ n`, where nothing truncates.  The generalisation costs almost
nothing, because **`Gsum_term_eq`'s hypothesis `r ≤ n` was never about `n`**: the proof uses it
only to reach `r ≤ m·k − 1`, which is exactly the range where `bin`'s truncation and the
generalized binomial's *own* vanishing coincide (`ringChoose_eq_zero_of_lt`).  Past `r = m·k` the
generalized factor is non-zero while `bin` is zero, and that difference is the correction.

So `Gsum` equals its untruncated closed form minus an explicit indicator-weighted sum, with no
hypothesis on `r` beyond `0 ≤ r`.  This is the `Gsum` half of `Link1d`'s remaining assembly; the
`dc` half is `Vt_inclExcl`.
-/

section GsumCorr

open Principia.Common

/-- `Gsum_term_eq` with its hypothesis weakened to what the proof actually uses: `r` strictly
below `m·k`, the point at which the generalized factor stops vanishing. -/
theorem Gsum_term_eq_gen {n j : ℕ} {r : ℤ} (h0 : 0 ≤ r)
    {k : ℕ} (hk1 : 1 ≤ k) (hkj : k ≤ j) (hr : r ≤ ((n : ℤ) + 1) * (k : ℤ) - 1) :
    bin ((j : ℤ) - (k : ℤ)) (r + (n : ℤ) * ((j : ℤ) - (k : ℤ)))
        * bin (k : ℤ) ((n : ℤ) * (k : ℤ) - 1 - r)
      = rothe ((n : ℤ) + 1) (j - k) r * rothe ((n : ℤ) + 1) k (-1 - r) := by
  have hn0 : (0 : ℤ) ≤ (n : ℤ) := Int.natCast_nonneg n
  have hjk : ((j - k : ℕ) : ℤ) = (j : ℤ) - (k : ℤ) := by omega
  have hk0 : (0 : ℤ) ≤ (k : ℤ) := Int.natCast_nonneg k
  have hM1 : (0 : ℤ) ≤ (j : ℤ) - (k : ℤ) := by omega
  have hU1 : (0 : ℤ) ≤ r + (n : ℤ) * ((j : ℤ) - (k : ℤ)) := by positivity
  have hkZ : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk1
  have hexp : ((n : ℤ) + 1) * (k : ℤ) = (n : ℤ) * (k : ℤ) + (k : ℤ) := by ring
  by_cases hU2 : (0 : ℤ) ≤ (n : ℤ) * (k : ℤ) - 1 - r
  · rw [bin_eq_ringChoose hM1 hU1, bin_eq_ringChoose hk0 hU2]
    simp only [rothe]
    congr 1 <;> congr 1 <;>
      first
        | (rw [hjk]; ring1)
        | ring1
        | omega
  · have hneg : (n : ℤ) * (k : ℤ) - 1 - r < 0 := by omega
    have he : (-1 - r) + ((n : ℤ) + 1) * (k : ℤ)
        = ((n : ℤ) * (k : ℤ) - 1 - r) + (k : ℤ) := by ring
    have hz : rothe ((n : ℤ) + 1) k (-1 - r) = 0 := by
      refine ringChoose_eq_zero_of_lt ?_ ?_
      · rw [he, hexp] at *
        linarith
      · rw [he]
        linarith
    rw [bin_of_neg hneg, mul_zero, hz, mul_zero]

/-- **`Gsum` off the untruncated range, with the correction named.**  No hypothesis on `r` beyond
`0 ≤ r`: past `r = m·k` the `k`-th generalized term survives while `bin` truncates, and the
indicator collects exactly those terms. -/
theorem Gsum_eq_sub_corr (n j : ℕ) {r : ℤ} (h0 : 0 ≤ r) :
    Gsum n j r
      = rotheConv ((n : ℤ) + 1) j 0 (-1) - Ring.choose (r + ((n : ℤ) + 1) * (j : ℤ)) j
        - ∑ k ∈ Finset.Icc 1 j,
            (if ((n : ℤ) + 1) * (k : ℤ) ≤ r then
              rothe ((n : ℤ) + 1) (j - k) r * rothe ((n : ℤ) + 1) k (-1 - r) else 0) := by
  classical
  have hconv : rotheConv ((n : ℤ) + 1) j r (-1 - r) = rotheConv ((n : ℤ) + 1) j 0 (-1) :=
    rotheConv_eq_of_add_eq _ j r (-1 - r) 0 (-1) (by ring)
  have hins : Finset.range (j + 1) = insert 0 (Finset.Icc 1 j) := by
    ext k
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  have hsplit : rotheConv ((n : ℤ) + 1) j r (-1 - r)
      = rothe ((n : ℤ) + 1) j r * rothe ((n : ℤ) + 1) 0 (-1 - r)
        + ∑ k ∈ Finset.Icc 1 j,
            rothe ((n : ℤ) + 1) (j - k) r * rothe ((n : ℤ) + 1) k (-1 - r) := by
    rw [rotheConv, hins, Finset.sum_insert (by simp)]
    simp
  have hzero : rothe ((n : ℤ) + 1) j r * rothe ((n : ℤ) + 1) 0 (-1 - r)
      = Ring.choose (r + ((n : ℤ) + 1) * (j : ℤ)) j := by
    simp [rothe]
  rw [Gsum_reindex]
  have hterms : ∀ k ∈ Finset.Icc 1 j,
      bin ((j : ℤ) - (k : ℤ)) (r + (n : ℤ) * ((j : ℤ) - (k : ℤ)))
          * bin (k : ℤ) ((n : ℤ) * (k : ℤ) - 1 - r)
        = rothe ((n : ℤ) + 1) (j - k) r * rothe ((n : ℤ) + 1) k (-1 - r)
          - (if ((n : ℤ) + 1) * (k : ℤ) ≤ r then
              rothe ((n : ℤ) + 1) (j - k) r * rothe ((n : ℤ) + 1) k (-1 - r) else 0) := by
    intro k hk
    have hk' := Finset.mem_Icc.mp hk
    have hkZ : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk'.1
    have hexp : ((n : ℤ) + 1) * (k : ℤ) = (n : ℤ) * (k : ℤ) + (k : ℤ) := by ring
    by_cases hbig : ((n : ℤ) + 1) * (k : ℤ) ≤ r
    · rw [if_pos hbig, sub_self]
      have hneg : (n : ℤ) * (k : ℤ) - 1 - r < 0 := by
        rw [hexp] at hbig
        linarith
      rw [bin_of_neg hneg, mul_zero]
    · rw [if_neg hbig, sub_zero]
      exact Gsum_term_eq_gen h0 hk'.1 hk'.2 (Int.le_sub_one_of_lt (not_le.mp hbig))
  rw [Finset.sum_congr rfl hterms, Finset.sum_sub_distrib]
  rw [hzero, hconv] at hsplit
  linarith [hsplit]

end GsumCorr

/-! ### The `dc` side off the untruncated range

`dc_low` needs `Vt n (i+1) r = C(r-1, i)`, which holds only for `r ≤ n`.  `Vt_inclExcl` replaces
that hypothesis unconditionally, so `dc` now has a closed form for every `s`: the same
Vandermonde-shaped outer sum, with each `Vt` expanded by inclusion–exclusion.  Stated at `j + 1`
for the reason `dc_low` is: at `j = 0` the `j - e` index would truncate.

This is the `dc` half of `Link1d`'s remaining assembly; the `Gsum` half is `Gsum_eq_sub_corr`.
-/

section DcCorr

open Principia.Common

/-- **`dc` in closed form for every `s`**, by expanding each `Vt` with `Vt_inclExcl`. -/
theorem dc_eq_sum_inclExcl (n j : ℕ) (s : ℤ) :
    (dc n (j + 1) s : ℤ)
      = ∑ e ∈ Finset.range (j + 1), (((j + 1) * (n + 1)).choose (j - e) : ℤ)
          * ∑ i ∈ Finset.range (e + 2), (-1 : ℤ) ^ i * ((e + 1).choose i : ℤ)
              * ibin (s - 1 - (n : ℤ) * (i : ℤ)) e := by
  classical
  have hreindex : dc n (j + 1) s
      = ∑ e ∈ Finset.range (j + 1),
          ((j + 1) * (n + 1)).choose (j - e) * Vt n (e + 1) s := by
    rw [dc]
    refine Finset.sum_nbij' (fun e => e - 1) (fun i => i + 1) ?_ ?_ ?_ ?_ ?_
    · intro e he
      simp only [Finset.mem_Icc] at he
      simp only [Finset.mem_range]
      omega
    · intro i hi
      simp only [Finset.mem_range] at hi
      simp only [Finset.mem_Icc]
      omega
    · intro e he
      simp only [Finset.mem_Icc] at he
      omega
    · intro i _
      omega
    · intro e he
      simp only [Finset.mem_Icc] at he
      have hidx : j + 1 - e = j - (e - 1) := by omega
      have hsucc : e - 1 + 1 = e := by omega
      rw [hidx, hsucc]
  rw [hreindex]
  push_cast
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Vt_inclExcl n e s]

end DcCorr

/-! ### `Link1d` assembled: one named obligation left

`Gsum_eq_sub_corr` and `dc_eq_sum_inclExcl` give both sides of `Link1d` unconditional closed
forms.  This section spends them, following the project's spine rule: the chain is written now,
with the single remaining gap as a **named `Prop`** (`CorrMatch`), so that the composition is a
typing fact rather than a plan.

Differencing the `Gsum` side in `r` is Pascal (`Ring.choose_succ_succ`), which produces exactly
the head term that the `dc` side's `i = 0` inclusion–exclusion slice produces by Vandermonde
(`vandermonde_range`).  Those two cancel, and what is left is `CorrMatch`: that the two
*corrections* agree.  Nothing else about `Link1d` remains.
-/

section LinkAssembly

open Principia.Common

/-- The `Gsum`-side correction: the terms `bin` truncates and the generalized binomial does not. -/
noncomputable def corr (n j : ℕ) (r : ℤ) : ℤ :=
  ∑ k ∈ Finset.Icc 1 j,
    (if ((n : ℤ) + 1) * (k : ℤ) ≤ r then
      rothe ((n : ℤ) + 1) (j - k) r * rothe ((n : ℤ) + 1) k (-1 - r) else 0)

/-- The `dc`-side correction: the `i ≥ 1` part of the inclusion–exclusion expansion. -/
def dcTail (n j : ℕ) (s : ℤ) : ℤ :=
  ∑ e ∈ Finset.range (j + 1), (((j + 1) * (n + 1)).choose (j - e) : ℤ)
    * ∑ i ∈ Finset.range (e + 1), (-1 : ℤ) ^ (i + 1) * ((e + 1).choose (i + 1) : ℤ)
        * ibin (s - 1 - (n : ℤ) * ((i : ℤ) + 1)) e

/-- **The one remaining obligation of `Link1d`.**  Everything else is discharged below. -/
def CorrMatch (n j : ℕ) : Prop :=
  ∀ r : ℤ, 1 ≤ r → corr n (j + 1) r - corr n (j + 1) (r - 1) = dcTail n j r

theorem Gsum_eq_sub_corr' (n j : ℕ) {r : ℤ} (h0 : 0 ≤ r) :
    Gsum n j r = rotheConv ((n : ℤ) + 1) j 0 (-1)
      - Ring.choose (r + ((n : ℤ) + 1) * (j : ℤ)) j - corr n j r := by
  rw [corr]
  exact Gsum_eq_sub_corr n j h0

/-- **The `dc` side splits into the untruncated head plus `dcTail`.**  The head is the `i = 0`
slice, and summing it over `e` is Vandermonde. -/
theorem dc_eq_head_add_tail (n j : ℕ) {s : ℤ} (hs : 1 ≤ s) :
    (dc n (j + 1) s : ℤ)
      = Ring.choose (s - 1 + ((n : ℤ) + 1) * ((j + 1 : ℕ) : ℤ)) j + dcTail n j s := by
  classical
  have hs0 : (0 : ℤ) ≤ s - 1 := by omega
  rw [dc_eq_sum_inclExcl, dcTail]
  have hsplit : ∀ e ∈ Finset.range (j + 1),
      (((j + 1) * (n + 1)).choose (j - e) : ℤ)
          * ∑ i ∈ Finset.range (e + 2), (-1 : ℤ) ^ i * ((e + 1).choose i : ℤ)
              * ibin (s - 1 - (n : ℤ) * (i : ℤ)) e
        = (((j + 1) * (n + 1)).choose (j - e) : ℤ) * ibin (s - 1) e
          + (((j + 1) * (n + 1)).choose (j - e) : ℤ)
              * ∑ i ∈ Finset.range (e + 1), (-1 : ℤ) ^ (i + 1) * ((e + 1).choose (i + 1) : ℤ)
                  * ibin (s - 1 - (n : ℤ) * ((i : ℤ) + 1)) e := by
    intro e _
    rw [Finset.sum_range_succ' (fun i => (-1 : ℤ) ^ i * ((e + 1).choose i : ℤ)
      * ibin (s - 1 - (n : ℤ) * (i : ℤ)) e) (e + 1)]
    have hhead : (-1 : ℤ) ^ 0 * ((e + 1).choose 0 : ℤ)
        * ibin (s - 1 - (n : ℤ) * ((0 : ℕ) : ℤ)) e = ibin (s - 1) e := by
      norm_num
    have htail : ∀ i ∈ Finset.range (e + 1),
        (-1 : ℤ) ^ (i + 1) * ((e + 1).choose (i + 1) : ℤ)
            * ibin (s - 1 - (n : ℤ) * ((i + 1 : ℕ) : ℤ)) e
          = (-1 : ℤ) ^ (i + 1) * ((e + 1).choose (i + 1) : ℤ)
              * ibin (s - 1 - (n : ℤ) * ((i : ℤ) + 1)) e := by
      intro i _
      have hc : ((i + 1 : ℕ) : ℤ) = (i : ℤ) + 1 := by push_cast; ring
      rw [hc]
    rw [Finset.sum_congr rfl htail, hhead]
    ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  congr 1
  -- the head sum is Vandermonde
  have hib : ∀ e : ℕ, ibin (s - 1) e = (((s - 1).toNat.choose e : ℕ) : ℤ) := by
    intro e
    rw [ibin_of_nonneg _ hs0]
  have hvan : ∑ e ∈ Finset.range (j + 1),
      ((j + 1) * (n + 1)).choose (j - e) * (s - 1).toNat.choose e
      = ((j + 1) * (n + 1) + (s - 1).toNat).choose j :=
    vandermonde_range ((j + 1) * (n + 1)) ((s - 1).toNat) j
  have hcast : ((((j + 1) * (n + 1) + (s - 1).toNat : ℕ) : ℤ))
      = s - 1 + ((n : ℤ) + 1) * ((j + 1 : ℕ) : ℤ) := by
    have h1 : (((s - 1).toNat : ℕ) : ℤ) = s - 1 := Int.toNat_of_nonneg hs0
    push_cast [h1]
    ring
  calc ∑ e ∈ Finset.range (j + 1), (((j + 1) * (n + 1)).choose (j - e) : ℤ) * ibin (s - 1) e
      = ((∑ e ∈ Finset.range (j + 1),
            ((j + 1) * (n + 1)).choose (j - e) * (s - 1).toNat.choose e : ℕ) : ℤ) := by
        push_cast
        exact Finset.sum_congr rfl fun e _ => by rw [hib e]
    _ = ((((j + 1) * (n + 1) + (s - 1).toNat).choose j : ℕ) : ℤ) := by rw [hvan]
    _ = Ring.choose (s - 1 + ((n : ℤ) + 1) * ((j + 1 : ℕ) : ℤ)) j := by
        rw [← hcast, Ring.choose_natCast]

/-- **`Link1d` for every `(n, j+1)`, modulo `CorrMatch`.**  The Pascal step on the `Gsum` side and
the Vandermonde head on the `dc` side cancel exactly; the corrections are all that is left. -/
theorem link1d_of_corrMatch (n j : ℕ) (h : CorrMatch n j) : Link1d n (j + 1) := by
  intro r hr
  have hG1 := Gsum_eq_sub_corr' n (j + 1) (r := r - 1) (by omega)
  have hG2 := Gsum_eq_sub_corr' n (j + 1) (r := r) (by omega)
  have hdc := dc_eq_head_add_tail n j (s := r) hr
  have hp := Ring.choose_succ_succ (r - 1 + ((n : ℤ) + 1) * ((j + 1 : ℕ) : ℤ)) j
  have e1 : r - 1 + ((n : ℤ) + 1) * ((j + 1 : ℕ) : ℤ) + 1
      = r + ((n : ℤ) + 1) * ((j + 1 : ℕ) : ℤ) := by ring
  rw [e1] at hp
  have hc := h r hr
  rw [hG1, hG2, hdc]
  linarith [hp, hc]

end LinkAssembly

/-! ### `CorrMatch`: the two corrections agree

The last obligation.  Three ingredients, none of them new mathematics:

* `rothe_neg_conv` — the generalized binomial at a negative argument is a **signed ordinary**
  one: `rothe m k (-1-r) = (-1)^k * Ring.choose (r - n*k) k`, unconditionally
  (`Ring.choose_neg` composed with `multichoose_eq`, since `m*k - 1 - r = -(r + 1 - m*k)` and
  `(r + 1 - m*k) + k - 1 = r - n*k`).
* `dcTail_swap` — `dcTail`'s inner range extends from `range (e+1)` to `range (j+1)` for free
  (`C(e+1, i+1) = 0` past `i = e`), after which `Finset.sum_comm` applies and the index shifts
  onto `corr`'s own `Icc 1 (j+1)`.
* `Principia.Common.choose_convolution_range` — at `t = (r - 1 - n*k).toNat`,
  `c = m*(j+1) - k`, `d = j+1-k`, `κ = k-1` its statement **is** the `k`-th slice: `d + κ = j`
  and `κ + 1 + c = m*(j+1)`.
-/

section CorrMatchProof

open Principia.Common

/-- **The generalized binomial at a negative argument is a signed ordinary one.**  No hypothesis
on `r`: this is an identity of `Ring.choose`. -/
theorem rothe_neg_conv (n k : ℕ) (r : ℤ) :
    rothe ((n : ℤ) + 1) k (-1 - r)
      = (-1 : ℤ) ^ k * Ring.choose (r - (n : ℤ) * (k : ℤ)) k := by
  have harg : (-1 - r) + ((n : ℤ) + 1) * (k : ℤ)
      = -(r + 1 - ((n : ℤ) + 1) * (k : ℤ)) := by ring
  have hz : (r + 1 - ((n : ℤ) + 1) * (k : ℤ)) + (k : ℤ) - 1
      = r - (n : ℤ) * (k : ℤ) := by ring
  simp only [rothe]
  rw [harg, Ring.choose_neg, hz]
  simp [Units.smul_def, Int.coe_negOnePow_natCast]

/-- The `k`-th slice of `dcTail`, after the swap. -/
noncomputable def dcSlice (n j : ℕ) (r : ℤ) (k : ℕ) : ℤ :=
  (-1 : ℤ) ^ k * ∑ e ∈ Finset.range (j + 1),
    (((j + 1) * (n + 1)).choose (j - e) : ℤ) * ((e + 1).choose k : ℤ)
      * ibin (r - 1 - (n : ℤ) * (k : ℤ)) e

/-- **`dcTail` reindexed onto `corr`'s index set.** -/
theorem dcTail_swap (n j : ℕ) (r : ℤ) :
    dcTail n j r = ∑ k ∈ Finset.Icc 1 (j + 1), dcSlice n j r k := by
  classical
  -- extend each inner range from `e+1` to `j+1`: the added terms vanish
  have hext : ∀ e ∈ Finset.range (j + 1),
      (((j + 1) * (n + 1)).choose (j - e) : ℤ)
          * ∑ i ∈ Finset.range (e + 1), (-1 : ℤ) ^ (i + 1) * ((e + 1).choose (i + 1) : ℤ)
              * ibin (r - 1 - (n : ℤ) * ((i : ℤ) + 1)) e
        = ∑ i ∈ Finset.range (j + 1),
            (((j + 1) * (n + 1)).choose (j - e) : ℤ) * ((-1 : ℤ) ^ (i + 1)
              * ((e + 1).choose (i + 1) : ℤ) * ibin (r - 1 - (n : ℤ) * ((i : ℤ) + 1)) e) := by
    intro e he
    have hej : e < j + 1 := Finset.mem_range.mp he
    rw [Finset.mul_sum]
    refine Finset.sum_subset ?_ ?_
    · intro i hi
      simp only [Finset.mem_range] at hi ⊢
      omega
    · intro i _ hni
      have hie : e + 1 < i + 1 := by
        simp only [Finset.mem_range] at hni
        omega
      have hz : ((e + 1).choose (i + 1) : ℤ) = 0 := by
        rw [Nat.choose_eq_zero_of_lt hie]
        norm_num
      rw [hz]
      ring
  rw [dcTail, Finset.sum_congr rfl hext, Finset.sum_comm]
  -- reindex `i` to `k = i + 1`
  refine (Finset.sum_nbij' (fun k => k - 1) (fun i => i + 1) ?_ ?_ ?_ ?_ ?_).symm
  · intro k hk
    simp only [Finset.mem_Icc] at hk
    simp only [Finset.mem_range]
    omega
  · intro i hi
    simp only [Finset.mem_range] at hi
    simp only [Finset.mem_Icc]
    omega
  · intro k hk
    simp only [Finset.mem_Icc] at hk
    omega
  · intro i _
    omega
  · intro k hk
    simp only [Finset.mem_Icc] at hk
    obtain ⟨hk1, hk2⟩ := hk
    have hks : k - 1 + 1 = k := by omega
    rw [dcSlice, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    have hc : ((k - 1 : ℕ) : ℤ) + 1 = (k : ℤ) := by omega
    rw [hks, hc]
    ring

/-- The slice vanishes below the indicator's threshold. -/
theorem dcSlice_eq_zero (n j : ℕ) {r : ℤ} {k : ℕ} (hk1 : 1 ≤ k)
    (hlt : r < ((n : ℤ) + 1) * (k : ℤ)) : dcSlice n j r k = 0 := by
  classical
  rw [dcSlice]
  have hz : ∀ e ∈ Finset.range (j + 1),
      (((j + 1) * (n + 1)).choose (j - e) : ℤ) * ((e + 1).choose k : ℤ)
          * ibin (r - 1 - (n : ℤ) * (k : ℤ)) e = 0 := by
    intro e _
    by_cases hek : e + 1 < k
    · rw [Nat.choose_eq_zero_of_lt hek]
      norm_num
    · -- `e + 1 >= k`, so `e >= k - 1 > r - 1 - n*k`, and the truncating binomial vanishes
      have hkz : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk1
      have hexp : ((n : ℤ) + 1) * (k : ℤ) = (n : ℤ) * (k : ℤ) + (k : ℤ) := by ring
      have hsmall : r - 1 - (n : ℤ) * (k : ℤ) < (k : ℤ) - 1 := by
        rw [hexp] at hlt
        linarith
      have hib : ibin (r - 1 - (n : ℤ) * (k : ℤ)) e = 0 := by
        rcases lt_or_ge (r - 1 - (n : ℤ) * (k : ℤ)) 0 with hneg | hnn
        · exact ibin_of_neg _ hneg
        · rw [ibin_of_nonneg _ hnn]
          have hlt2 : (r - 1 - (n : ℤ) * (k : ℤ)).toNat < e := by omega
          rw [Nat.choose_eq_zero_of_lt hlt2]
          norm_num
      rw [hib]
      ring
  rw [Finset.sum_congr rfl hz, Finset.sum_const_zero, mul_zero]

/-- **The slice above the threshold is the `k`-th correction difference.**  This is
`choose_convolution_range`, with every `Ring.choose` at a nonnegative argument. -/
theorem dcSlice_eq_diff (n j : ℕ) {r : ℤ} {k : ℕ} (hk1 : 1 ≤ k) (hkj : k ≤ j + 1)
    (hle : ((n : ℤ) + 1) * (k : ℤ) ≤ r) :
    dcSlice n j r k
      = rothe ((n : ℤ) + 1) (j + 1 - k) r * rothe ((n : ℤ) + 1) k (-1 - r)
        - rothe ((n : ℤ) + 1) (j + 1 - k) (r - 1) * rothe ((n : ℤ) + 1) k (-1 - (r - 1)) := by
  classical
  have hkz : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk1
  have hexp : ((n : ℤ) + 1) * (k : ℤ) = (n : ℤ) * (k : ℤ) + (k : ℤ) := by ring
  have hnn : (0 : ℤ) ≤ r - 1 - (n : ℤ) * (k : ℤ) := by
    rw [hexp] at hle
    linarith
  set t : ℕ := (r - 1 - (n : ℤ) * (k : ℤ)).toNat with ht
  have htz : ((t : ℕ) : ℤ) = r - 1 - (n : ℤ) * (k : ℤ) := Int.toNat_of_nonneg hnn
  set c : ℕ := (j + 1) * (n + 1) - k with hc
  set d : ℕ := j + 1 - k with hd
  have hkle : k ≤ (j + 1) * (n + 1) := by
    have : j + 1 ≤ (j + 1) * (n + 1) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have hcz : ((c : ℕ) : ℤ) = ((j + 1) * (n + 1) : ℕ) - (k : ℤ) := by
    rw [hc]; omega
  have hdz : ((d : ℕ) : ℤ) = (j : ℤ) + 1 - (k : ℤ) := by
    rw [hd]; omega
  -- the four `Ring.choose` values, as ordinary binomials
  have hA : Ring.choose (r - (n : ℤ) * (k : ℤ)) k = (((t + 1).choose k : ℕ) : ℤ) := by
    have : r - (n : ℤ) * (k : ℤ) = ((t + 1 : ℕ) : ℤ) := by push_cast [htz]; ring
    rw [this, Ring.choose_natCast]
  have hB : Ring.choose (r - 1 - (n : ℤ) * (k : ℤ)) k = ((t.choose k : ℕ) : ℤ) := by
    rw [← htz, Ring.choose_natCast]
  have hC : rothe ((n : ℤ) + 1) d r = (((t + 1 + c).choose d : ℕ) : ℤ) := by
    have harg : r + ((n : ℤ) + 1) * ((d : ℕ) : ℤ) = ((t + 1 + c : ℕ) : ℤ) := by
      rw [hdz]; push_cast [htz, hcz]; ring
    simp only [rothe]
    rw [harg, Ring.choose_natCast]
  have hD : rothe ((n : ℤ) + 1) d (r - 1) = (((t + c).choose d : ℕ) : ℤ) := by
    have harg : (r - 1) + ((n : ℤ) + 1) * ((d : ℕ) : ℤ) = ((t + c : ℕ) : ℤ) := by
      rw [hdz]; push_cast [htz, hcz]; ring
    simp only [rothe]
    rw [harg, Ring.choose_natCast]
  -- the two sign conversions
  rw [rothe_neg_conv, rothe_neg_conv]
  have hr1 : (r - 1) - (n : ℤ) * (k : ℤ) = r - 1 - (n : ℤ) * (k : ℤ) := by ring
  rw [hr1, hA, hB, hC, hD]
  -- and now the identity is `choose_convolution_range`
  obtain ⟨kk, hkk⟩ : ∃ kk, k = kk + 1 := ⟨k - 1, by omega⟩
  have hkey := choose_convolution_range t c d kk
  have hdk : d + kk = j := by omega
  have hck : kk + 1 + c = (j + 1) * (n + 1) := by omega
  rw [hdk, hck, ← hkk] at hkey
  have hcastZ : (((t + 1 + c).choose d : ℕ) : ℤ) * (((t + 1).choose k : ℕ) : ℤ)
      = (((t + c).choose d : ℕ) : ℤ) * ((t.choose k : ℕ) : ℤ)
        + ∑ e ∈ Finset.range (j + 1),
            ((((j + 1) * (n + 1)).choose (j - e) : ℕ) : ℤ) * (((e + 1).choose k : ℕ) : ℤ)
              * ((t.choose e : ℕ) : ℤ) := by
    exact_mod_cast hkey
  have hterms : ∀ e ∈ Finset.range (j + 1),
      ((((j + 1) * (n + 1)).choose (j - e) : ℕ) : ℤ) * (((e + 1).choose k : ℕ) : ℤ)
          * ibin (r - 1 - (n : ℤ) * (k : ℤ)) e
        = ((((j + 1) * (n + 1)).choose (j - e) : ℕ) : ℤ) * (((e + 1).choose k : ℕ) : ℤ)
            * ((t.choose e : ℕ) : ℤ) := by
    intro e _
    have hib : ibin (r - 1 - (n : ℤ) * (k : ℤ)) e = ((t.choose e : ℕ) : ℤ) := by
      rw [ibin_of_nonneg _ hnn, ← ht]
    rw [hib]
  rw [dcSlice, Finset.sum_congr rfl hterms]
  linear_combination (-((-1 : ℤ) ^ k)) * hcastZ

end CorrMatchProof

section CorrMatchFinal

open Principia.Common

/-- **`CorrMatch` holds**: termwise, with three cases.  Above the threshold the slice is the
correction difference (`dcSlice_eq_diff`); at `r = m*k` exactly, the `r-1` term is absent from
`corr` and vanishes anyway, because `rothe m k (-1-(r-1))` is `Ring.choose 0 k = 0`; below the
threshold both sides are zero (`dcSlice_eq_zero`). -/
theorem corrMatch_holds (n j : ℕ) : CorrMatch n j := by
  classical
  intro r hr
  rw [corr, corr, ← Finset.sum_sub_distrib, dcTail_swap]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_Icc.mp hk
  have hkz : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk'.1
  by_cases hle : ((n : ℤ) + 1) * (k : ℤ) ≤ r
  · rw [if_pos hle, dcSlice_eq_diff n j hk'.1 hk'.2 hle]
    by_cases hle' : ((n : ℤ) + 1) * (k : ℤ) ≤ r - 1
    · rw [if_pos hle']
    · rw [if_neg hle']
      have hreq : ((n : ℤ) + 1) * (k : ℤ) = r := by
        have hlt := not_le.mp hle'
        linarith
      have hzero : rothe ((n : ℤ) + 1) k (-1 - (r - 1)) = 0 := by
        simp only [rothe]
        have harg : (-1 - (r - 1)) + ((n : ℤ) + 1) * (k : ℤ) = 0 := by rw [hreq]; ring
        rw [harg]
        exact ringChoose_eq_zero_of_lt (le_refl 0) (by linarith)
      rw [hzero, mul_zero, sub_zero]
  · rw [if_neg hle, dcSlice_eq_zero n j hk'.1 (not_le.mp hle)]
    have hle' : ¬ (((n : ℤ) + 1) * (k : ℤ) ≤ r - 1) := by
      intro h
      exact hle (by linarith)
    rw [if_neg hle']
    ring

/-- **`Link1d` for every `(n, j)`.**  At `j = 0` both sides are empty sums. -/
theorem link1d_all (n j : ℕ) : Link1d n j := by
  cases j with
  | zero =>
      intro r _
      simp [Gsum, dc]
  | succ j => exact link1d_of_corrMatch n j (corrMatch_holds n j)

/-- **THE CONJECTURE, unconditionally, for every `n`, every `j`, and every odd `psi`.**  Svinin's
generalized power-sum identity, in the write-up's extension to an arbitrary odd function. -/
theorem main_unconditional (psi : ℤ → ℂ) (n j : ℕ) (hodd : ∀ r : ℤ, psi (-r) = -psi r) :
    LHS psi n j = RHS psi n j :=
  main_of_link1d psi n j hodd (link1d_all n j)

/-- **The literal conjecture**: Svinin's display at `psi = (·)^(2k+1)`, which is odd, for every
`n`, `j` and `k`.  The write-up proves the stronger arbitrary-odd-`psi` form
(`main_unconditional`); this instantiation is recorded so that the source's own statement is
visibly delivered and not merely implied. -/
theorem main_odd_power (n j k : ℕ) :
    LHS (fun r => (r : ℂ) ^ (2 * k + 1)) n j = RHS (fun r => (r : ℂ) ^ (2 * k + 1)) n j := by
  refine main_unconditional _ n j ?_
  intro r
  have hodd : Odd (2 * k + 1) := ⟨k, by ring⟩
  push_cast
  rw [hodd.neg_pow]

end CorrMatchFinal

end Principia.MathDB.P334350
