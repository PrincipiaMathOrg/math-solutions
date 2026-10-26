import Mathlib

/-!
# MathDB #360955 — unimodality of plucking polynomials of stars with delays in `{1,2}`

Write-up `mathdb-open-problems/problems/360955/solution.tex`,
*Unimodality of plucking polynomials of hedgehog rooted trees*, 18 September 2026.

A finite nonnegative sequence is **unimodal** when it is weakly increasing up to some index and
weakly decreasing thereafter; a polynomial is unimodal when its coefficient sequence is.  With
`[r]_q = 1 + q + ⋯ + q^{r-1}` and `[r]_q! = ∏_{j≤r} [j]_q`, Conjecture 4.1 of Ilyutko–Manturov et
al. asks whether the plucking polynomial `Q(T,f)` of a star whose leaf delays lie in `{1,2}` is
always unimodal.

**It is**, and the proof is entirely elementary.  Source Proposition 2.5 — a **credited input**,
not proved here — factors it as `Q(T,f) = A(q)·[n−1]_q!` where `A = ∑ ε_i q^i` with `ε_i ∈ {0,1}`
and `deg A ≤ n−1`.  Two lemmas then finish it:

* `long` — for `A` of degree at most `m` with nonnegative coefficients, `A(q)[m]_q` is unimodal.
  Its coefficients are prefix sums of `A` up to index `m−1` and suffix sums from `m`, so it rises
  then falls; the single ambiguous comparison is `b_m − b_{m−1} = a_m − a_0`, whose sign picks the
  peak out of `{m−1, m}`.
* `moving` — multiplying a nonnegative **unimodal** polynomial by `[r]_q` preserves unimodality.

`main` composes them: one long factor `[m]_q` creates unimodality, and every remaining factor of
`[m]_q!` preserves it.  `plucking` specialises to the `{0,1}` coefficients of the conjecture.

## Two things worth pointing at

**Indices are `ℤ`, not `ℕ`.**  A window reaching below `0` then simply reads zeros, instead of
hitting truncated `ℕ` subtraction — which would silently fold `c (i - t)` back onto `c 0`.

**The peak of a product is NOT localised near the peak of the factor.**  An earlier plan proved
`moving` by placing the new peak inside `[p−1, p+r−1]`; that is false, as plateaus and the zero
sequence show.  What is true, and what `moving` uses, is that the product's successive
differences `c(i+1) − c(i+1−r)` change sign at most once (`step_down_persists`), so the peak can
be taken to be the **least index at which the product strictly drops** — and when there is no
such index the product is identically zero, being non-decreasing with finite support.

## Scope

`main` is proved for arbitrary **nonnegative real** coefficients, which is stronger than the
`{0,1}` case the conjecture needs, and matches the extension the write-up claims.  Not formalized:
Proposition 2.5 itself (the factorization), nor the combinatorics of plucking — the write-up
credits both to the source.  The write-up also records **zero campaign credit pending a source
audit**, the published 2026 chapter being unavailable for comparison; that is the collaborator's
accounting, not a mathematical qualification.

Checked in Python before formalizing (`verify_360955.py`, `verify_360955_moving.py`): `long` over
`m ≤ 11` with 400 random `A` each, plus its explicit coefficient formula and
`b_m − b_{m−1} = a_m − a_0`; `moving` over 4000 random unimodal inputs; the main claim for
`n ≤ 8` with `{0,1}` coefficients and for nonnegative rationals; and, separately, each
sub-implication the Lean proof of `moving` uses — including the one that failed, which is how the
false peak-localisation plan was caught before any Lean was written.
-/

namespace Principia.MathDB.P360955

open Finset

/-- Coefficient sequences are indexed by `ℤ`, so that a window reaching below `0` simply reads
zeros instead of hitting truncated `ℕ` subtraction. -/
abbrev Coef := ℤ → ℝ

/-- The source's notion: weakly increasing up to some index, weakly decreasing thereafter. -/
def Unimodal (c : Coef) : Prop :=
  ∃ p : ℤ, (∀ i j : ℤ, i ≤ j → j ≤ p → c i ≤ c j) ∧ (∀ i j : ℤ, p ≤ i → i ≤ j → c j ≤ c i)

/-- Coefficients of `B(q) · [r]_q`: the sliding window sum of length `r`. -/
def window (r : ℕ) (c : Coef) (i : ℤ) : ℝ := ∑ t ∈ range r, c (i - t)

/-- **The workhorse.**  Successive window sums differ by one entering and one leaving term. -/
theorem window_succ_sub (r : ℕ) (hr : 1 ≤ r) (c : Coef) (i : ℤ) :
    window r c (i + 1) - window r c i = c (i + 1) - c (i + 1 - r) := by
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  unfold window
  rw [Finset.sum_range_succ' (fun t => c (i + 1 - t)) s,
    Finset.sum_range_succ (fun t => c (i - t)) s]
  -- `push_cast` first: `sum_range_succ'` leaves `↑(t+1)`, while the target carries `↑t + 1`.
  push_cast
  rw [show (∑ t ∈ range s, c (i + 1 - ((t : ℤ) + 1))) = ∑ t ∈ range s, c (i - (t : ℤ)) from
    Finset.sum_congr rfl (fun t _ => by congr 1; ring)]
  ring

/-- A sequence supported on `[0, m]` with nonnegative entries. -/
structure Supp (a : Coef) (m : ℕ) : Prop where
  nonneg : ∀ i, 0 ≤ a i
  below : ∀ i : ℤ, i < 0 → a i = 0
  above : ∀ i : ℤ, (m : ℤ) < i → a i = 0

/-- Step-to-range, upward: a pointwise step below `p` gives monotonicity on `(-∞, p]`. -/
theorem mono_up (f : ℤ → ℝ) (p : ℤ) (h : ∀ i : ℤ, i + 1 ≤ p → f i ≤ f (i + 1)) :
    ∀ (n : ℕ) (i : ℤ), i + n ≤ p → f i ≤ f (i + n) := by
  intro n
  induction n with
  | zero => intro i _; simp
  | succ k ih =>
    intro i hi
    have hk : i + (k : ℤ) ≤ p := by push_cast at hi; omega
    have h1 : f i ≤ f (i + k) := ih i hk
    have h2 : f (i + k) ≤ f (i + k + 1) := h (i + k) (by push_cast at hi; omega)
    have e : i + ((k : ℕ) + 1 : ℕ) = i + (k : ℤ) + 1 := by push_cast; ring
    rw [e]
    linarith

/-- Step-to-range, downward: a pointwise step above `p` gives antitonicity on `[p, ∞)`. -/
theorem mono_dn (f : ℤ → ℝ) (p : ℤ) (h : ∀ i : ℤ, p ≤ i → f (i + 1) ≤ f i) :
    ∀ (n : ℕ) (i : ℤ), p ≤ i → f (i + n) ≤ f i := by
  intro n
  induction n with
  | zero => intro i _; simp
  | succ k ih =>
    intro i hi
    have h1 : f (i + k) ≤ f i := ih i hi
    have h2 : f (i + k + 1) ≤ f (i + k) := h (i + k) (by omega)
    have e : i + ((k : ℕ) + 1 : ℕ) = i + (k : ℤ) + 1 := by push_cast; ring
    rw [e]
    linarith

/-- Package the two step facts into `Unimodal`, given a peak candidate. -/
theorem unimodal_of_steps (f : ℤ → ℝ) (p : ℤ)
    (hup : ∀ i : ℤ, i + 1 ≤ p → f i ≤ f (i + 1))
    (hdn : ∀ i : ℤ, p ≤ i → f (i + 1) ≤ f i) : Unimodal f := by
  refine ⟨p, ?_, ?_⟩
  · intro i j hij hjp
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, j = i + n := ⟨(j - i).toNat, by omega⟩
    exact mono_up f p hup n i hjp
  · intro i j hpi hij
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, j = i + n := ⟨(j - i).toNat, by omega⟩
    exact mono_dn f p hdn n i hpi

/-- **Lemma `long`.**  For `A` of degree at most `m` with nonnegative coefficients,
`A(q)·[m]_q` is unimodal: the coefficients are prefix sums up to `m−1` and suffix sums from `m`. -/
theorem long (m : ℕ) (hm : 1 ≤ m) (a : Coef) (ha : Supp a m) : Unimodal (window m a) := by
  have key : ∀ i : ℤ, window m a (i + 1) - window m a i = a (i + 1) - a (i + 1 - m) :=
    fun i => window_succ_sub m hm a i
  -- rising while `i + 1 ≤ m − 1`
  have up : ∀ i : ℤ, i + 1 ≤ (m : ℤ) - 1 → window m a i ≤ window m a (i + 1) := by
    intro i hi
    have h0 : a (i + 1 - m) = 0 := ha.below _ (by omega)
    have := key i
    rw [h0, sub_zero] at this
    have := ha.nonneg (i + 1)
    linarith [key i, ha.nonneg (i + 1), h0]
  -- falling once `i ≥ m`
  have dn : ∀ i : ℤ, (m : ℤ) ≤ i → window m a (i + 1) ≤ window m a i := by
    intro i hi
    have h0 : a (i + 1) = 0 := ha.above _ (by omega)
    have := key i
    rw [h0] at this
    linarith [ha.nonneg (i + 1 - m)]
  -- the single ambiguous comparison is `b (m-1)` against `b m`; it fixes the peak
  by_cases hpk : window m a ((m : ℤ) - 1) ≤ window m a (m : ℤ)
  · refine unimodal_of_steps _ (m : ℤ) (fun i hi => ?_) (fun i hi => dn i hi)
    rcases eq_or_lt_of_le hi with he | hlt
    · have : i = (m : ℤ) - 1 := by omega
      subst this
      simpa using hpk
    · exact up i (by omega)
  · refine unimodal_of_steps _ ((m : ℤ) - 1) (fun i hi => up i (by omega)) (fun i hi => ?_)
    rcases eq_or_lt_of_le hi with he | hlt
    · have : i = (m : ℤ) - 1 := by omega
      subst this
      have : window m a (m : ℤ) ≤ window m a ((m : ℤ) - 1) := (not_le.mp hpk).le
      simpa using this
    · exact dn i (by omega)

/-- **The heart of `moving`.**  Once a window sum strictly decreases it never increases again.
The proof is a two-case split on whether the LEAVING index `j+1-r` has passed the peak. -/
theorem step_down_persists (r : ℕ) (hr : 1 ≤ r) (c : Coef) (p : ℤ)
    (hup : ∀ i j : ℤ, i ≤ j → j ≤ p → c i ≤ c j)
    (hdn : ∀ i j : ℤ, p ≤ i → i ≤ j → c j ≤ c i)
    (i : ℤ) (hi : c (i + 1) - c (i + 1 - r) < 0) :
    ∀ j : ℤ, i ≤ j → c (j + 1) - c (j + 1 - r) ≤ 0 := by
  intro j hj
  -- a strict drop can only happen after the peak
  have hip : p < i + 1 := by
    by_contra h
    push_neg at h
    have := hup (i + 1 - r) (i + 1) (by omega) h
    linarith
  by_cases hc : p ≤ j + 1 - r
  · -- both endpoints past the peak: `c` is decreasing there
    have := hdn (j + 1 - r) (j + 1) hc (by omega)
    linarith
  · -- the leaving index is still before the peak, so it has only grown,
    -- while the entering index has only shrunk
    push_neg at hc
    have h1 : c (j + 1) ≤ c (i + 1) := hdn (i + 1) (j + 1) (by omega) (by omega)
    have h2 : c (i + 1 - r) ≤ c (j + 1 - r) := hup (i + 1 - r) (j + 1 - r) (by omega) (by omega)
    linarith

/-- Window sums inherit finite support.  The bound `D + r` is deliberately loose (the sharp one
is `D + r - 1`); looseness costs nothing downstream and avoids a `ℕ` subtraction. -/
theorem window_supp (r : ℕ) (b : Coef) (D : ℕ) (hb : Supp b D) :
    Supp (window r b) (D + r) where
  nonneg i := Finset.sum_nonneg fun t _ => hb.nonneg _
  below i hi := Finset.sum_eq_zero fun t ht => hb.below _ (by
    have : (0 : ℤ) ≤ (t : ℤ) := Int.natCast_nonneg t
    omega)
  above i hi := Finset.sum_eq_zero fun t ht => hb.above _ (by
    rw [Finset.mem_range] at ht
    have : (t : ℤ) < r := by exact_mod_cast ht
    push_cast at hi
    omega)

/-- **Lemma `moving`.**  Multiplying a nonnegative unimodal polynomial by `[r]_q` preserves
unimodality.  The peak of the product is the LEAST index at which it strictly drops; when there
is no such index the product is identically zero, because it is non-decreasing with finite
support.  (An earlier plan located the new peak inside `[p-1, p+r-1]`; that is FALSE — plateaus
and the zero sequence break it, which a numerical check caught before any Lean was written.) -/
theorem moving (r : ℕ) (hr : 1 ≤ r) (b : Coef) (D : ℕ) (hb : Supp b D) (hu : Unimodal b) :
    Unimodal (window r b) := by
  classical
  obtain ⟨p, hup, hdn⟩ := hu
  have hd : ∀ i : ℤ, window r b (i + 1) - window r b i = b (i + 1) - b (i + 1 - r) :=
    fun i => window_succ_sub r hr b i
  have hsupp := window_supp r b D hb
  by_cases hex : ∃ i : ℤ, window r b (i + 1) < window r b i
  · -- the peak is the LEAST index at which the product strictly drops
    obtain ⟨q, hq, hmin⟩ :
        ∃ q : ℤ, window r b (q + 1) < window r b q ∧
          ∀ z : ℤ, window r b (z + 1) < window r b z → q ≤ z := by
      refine Int.exists_least_of_bdd ?_ hex
      refine ⟨-(D : ℤ) - r - 1, ?_⟩
      intro z hz
      by_contra hlt
      push_neg at hlt
      rw [hsupp.below (z + 1) (by omega), hsupp.below z (by omega)] at hz
      exact lt_irrefl _ hz
    refine unimodal_of_steps _ q (fun i hi => ?_) (fun i hi => ?_)
    · -- below the least drop there is no drop, so the step is upward
      by_contra hcon
      push_neg at hcon
      have := hmin i hcon
      omega
    · -- at or above it, the drop persists
      have hqneg : b (q + 1) - b (q + 1 - r) < 0 := by have := hd q; linarith
      have hpers := step_down_persists r hr b p hup hdn q hqneg i hi
      have := hd i
      linarith
  · -- no drop anywhere: non-decreasing with finite support forces the zero sequence
    push_neg at hex
    have hstep : ∀ i : ℤ, window r b i ≤ window r b (i + 1) := hex
    have hzero : ∀ i : ℤ, window r b i = 0 := by
      intro i
      refine le_antisymm ?_ (hsupp.nonneg i)
      by_cases hle : i ≤ (D : ℤ) + r + 1
      · obtain ⟨n, hn⟩ : ∃ n : ℕ, (D : ℤ) + r + 1 = i + n := ⟨((D : ℤ) + r + 1 - i).toNat, by omega⟩
        have := mono_up (window r b) ((D : ℤ) + r + 1)
          (fun k _ => hstep k) n i (by omega)
        rw [← hn] at this
        -- name the index: a bare `_` lets `rw` match the LEFTMOST occurrence, which is
        -- `window r b i`, not the endpoint we mean to send to zero.
        rw [hsupp.above ((D : ℤ) + r + 1) (by push_cast; omega)] at this
        exact this
      · push_neg at hle
        exact le_of_eq (hsupp.above i (by push_cast; omega))
    refine ⟨0, fun i j _ _ => ?_, fun i j _ _ => ?_⟩ <;> rw [hzero, hzero]

/-- Multiply by `[k]_q · [k-1]_q ⋯ [1]_q`, one factor at a time.  With `k = m` this is
multiplication by `[m]_q!`. -/
def qfactWindow : ℕ → Coef → Coef
  | 0, c => c
  | (k + 1), c => qfactWindow k (window (k + 1) c)

/-- Each remaining quantum-integer factor preserves unimodality, by `moving`. -/
theorem qfact_preserves : ∀ (k : ℕ) (c : Coef) (D : ℕ), Supp c D → Unimodal c →
    Unimodal (qfactWindow k c) := by
  intro k
  induction k with
  | zero => intro c _ _ hu; exact hu
  | succ j ih =>
    intro c D hs hu
    exact ih (window (j + 1) c) (D + (j + 1)) (window_supp _ c D hs)
      (moving (j + 1) (by omega) c D hs hu)

/-- **The theorem.**  For `A` of degree at most `m` with nonnegative coefficients,
`A(q) · [m]_q!` is unimodal.  One long factor `[m]_q` makes it unimodal (`long`); every further
factor preserves that (`moving`). -/
theorem main (m : ℕ) (hm : 1 ≤ m) (a : Coef) (ha : Supp a m) :
    Unimodal (qfactWindow m a) := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  show Unimodal (qfactWindow j (window (j + 1) a))
  exact qfact_preserves j (window (j + 1) a) ((j + 1) + (j + 1))
    (window_supp _ a _ ha) (long (j + 1) hm a ha)

/-- **The conjecture's case.**  The plucking polynomial of a star with leaf delays in `{1,2}`
factors (source Prop 2.5, a credited input) as `A(q)[n-1]_q!` with `A = ∑ ε_i q^i`,
`ε_i ∈ {0,1}`, `deg A ≤ n-1`.  Such a product is unimodal. -/
theorem plucking (n : ℕ) (hn : 2 ≤ n) (eps : Coef)
    (h01 : ∀ i, eps i = 0 ∨ eps i = 1)
    (hlo : ∀ i : ℤ, i < 0 → eps i = 0)
    (hhi : ∀ i : ℤ, ((n : ℤ) - 1) < i → eps i = 0) :
    Unimodal (qfactWindow (n - 1) eps) := by
  refine main (n - 1) (by omega) eps ⟨fun i => ?_, hlo, fun i hi => hhi i ?_⟩
  · rcases h01 i with h | h <;> rw [h] <;> norm_num
  · have : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by
      have : 1 ≤ n := by omega
      push_cast [Nat.cast_sub this]
      ring
    omega

end Principia.MathDB.P360955
