import Mathlib.Tactic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Polynomial

set_option autoImplicit false

/-!
# MathDB 323156 — positive coefficients of rising-factorial Turán polynomials

Write-up: `mathdb-open-problems/problems/323156/solution.tex` on the `mathdb-results`
branch of `antoshashakov/Principia-Math-In-Progress`.  It proves **Karp's Conjecture 1**.

With `(v)_k = v(v+1)⋯(v+k-1)`, a nonnegative sequence `(f_k)` and `α, β > 0`,

    Q(x) = ∑_{k+m = n} C(n,k) f_k f_m [ (x+α)_k (x+β)_m - (x+α+β)_k (x)_m ].

The theorem: if `n ≥ 3` and `(f_k)` is strictly log-concave on the interior
(`f_k² > f_{k-1} f_{k+1}` for `1 ≤ k ≤ n-1`), then `Q` has degree `n-2` and a strictly
positive coefficient at every `x^j`, `0 ≤ j ≤ n-2`.

## Status: SPINE, not a finished row

Following the project's spine rule, the chain to the goal is complete and every gap is a
named hypothesis.  What is **proved** here is the write-up's assembly half; what is
**carried** is its technical core.  See `Setup` for the single carried obligation.

## What is proved

* `rising_vandermonde` — the rising-factorial Chu–Vandermonde identity
  `∑_{i+j=n} C(n,i) (a)_i (b)_j = (a+b)_n` in any commutative ring.  **Mathlib has only
  the descending version** (`descPochhammer_smeval_add`), so this is new, and it is
  campaign-agnostic: a promotion candidate for `Principia/Common/`.
* `V_zero` — hence `V n 0 = 0`: at `r = 0` both halves of the bracket collapse to the
  same Vandermonde value, because `(x+α) + (x+β) = (x+α+β) + x`.  This is the structural
  fact behind the whole theorem: **`Q` measures the deviation from Vandermonde**, which
  is why strict log-concavity (rather than plain log-concavity) is the hypothesis — for
  `f ≡ 1` the polynomial vanishes identically.
* `interior_pos` — strict log-concavity forces `f_k > 0` for `1 ≤ k ≤ n-1` (an interior
  zero would give `0 = f_k² > f_{k-1} f_{k+1} ≥ 0`).
* `spread` — the log-concavity chain `f_a f_b > f_{a-1} f_{b+1}` for `1 ≤ a ≤ b ≤ n-1`,
  by induction on `b`, cancelling the interior `f_b > 0`.
* `weight_lt` — so the weights `W j = f j * f (n-j)` strictly increase up to `⌊n/2⌋`.
* `decomposition` — the write-up's summation by parts,
  `Q = ∑_{r=1}^{⌊n/2⌋} (W r - W (r-1)) • V n r`, by a layer-cake rewrite of `W` and one
  exchange of finite sums.
* `V_natDegree_le` and `Q_natDegree_le` — **the degree really is `n-2`**, by two separate
  cancellations.  Each `term` is a difference of two *monic* degree-`n` products, which
  kills `xⁿ`.  The `x^{n-1}` coefficient does **not** vanish termwise — it is `(m-k)β`,
  computed via `nextCoeff` — and cancels only after summing, by `Finset.sum_involution`
  under the swap `(k,m) ↦ (m,k)`, which preserves the filter range while
  `C(n,k) = C(n,m)` on the antidiagonal.

## What is carried

**One field, `Setup.V_coeff_pos`**: that each central truncation `V n r` has a strictly
positive coefficient at every `x^j`, `0 ≤ j ≤ n-2`.  That is the write-up's technical
core — a two-variable derivative identity `(∂_A-∂_B) C_{n,r} = (B-A) R_{n,r}` with
`R_{n,r}` nonnegative, then integration along `A = x+t`, `B = x+c-t`.  It is not proved
here.  (The companion degree bound was carried in the first draft of this module and is
now proved, so the carry is strictly smaller than it was.)

Indices are carried as `Finset.antidiagonal` pairs throughout rather than `k` and `n-k`,
which removes every `ℕ`-subtraction from the sums and makes the weight symmetry
`f p.1 * f p.2` definitional.

Python check: `Campaigns/MathDB-Formalization/verify_323156.py` — sympy over exact
rationals; it confirms every step of the write-up symbolically, including that `Q`
vanishes identically for `f ≡ 1`.
-/

namespace Principia.MathDB.P323156

open Finset Polynomial

/-! ### Rising factorials and Chu–Vandermonde -/

section Ring

variable {R : Type*} [CommRing R]

/-- `rising a k = a(a+1)⋯(a+k-1)`. -/
def rising (a : R) (k : ℕ) : R := ∏ i ∈ range k, (a + (i : R))

@[simp] lemma rising_zero (a : R) : rising a 0 = 1 := by simp [rising]

lemma rising_succ (a : R) (k : ℕ) : rising a (k + 1) = rising a k * (a + (k : R)) := by
  simp [rising, Finset.prod_range_succ]

/-- **Rising-factorial Chu–Vandermonde.**  Mathlib has the descending version
(`descPochhammer_smeval_add`) but not this one. -/
theorem rising_vandermonde (n : ℕ) (a b : R) :
    ∑ p ∈ antidiagonal n, (n.choose p.1 : R) * (rising a p.1 * rising b p.2)
      = rising (a + b) n := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [sum_antidiagonal_choose_succ_mul (fun i j => rising a i * rising b j) m]
    have key : ∀ p ∈ antidiagonal m,
        (m.choose p.1 : R) * (rising a p.1 * rising b (p.2 + 1))
          + (m.choose p.2 : R) * (rising a (p.1 + 1) * rising b p.2)
          = (m.choose p.1 : R) * (rising a p.1 * rising b p.2) * (a + b + (m : R)) := by
      intro p hp
      have hsum : p.1 + p.2 = m := by simpa using hp
      have hch : m.choose p.2 = m.choose p.1 := Nat.choose_symm_of_eq_add (by omega)
      rw [hch, rising_succ, rising_succ, ← hsum]
      push_cast
      ring
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl key, ← Finset.sum_mul, ih, rising_succ]

/-! ### Toward `V_coeff_pos`: the write-up's Lemma 1

Two pieces of Lemma 1 are here.  `derivative_rising` is the identity the write-up
differentiates with.  `sum_sub_sum_swap` is the reflection cancellation, and
`sum_sub_sum_swap_range` — which consumes it — is the write-up's boundary equation
in index-only form: with `L ≤ r` the two one-sided constraints differ exactly on
`L ≤ k < r`, which with `k + m = N` and `r ≤ m` is its `L ≤ k ≤ min(r-1, N-r)`.
Still missing for Lemma 1: the bracket factorisation and the divided difference
that build `R_{n,r}`.  `derivative_rising` is not yet consumed; the swap pair is. -/

lemma rising_mul_shift (a : R) (j k : ℕ) (h : j ≤ k) :
    rising a j * (a + (k : R)) = rising a (j + 1) + ((k - j : ℕ) : R) * rising a j := by
  rw [rising_succ]
  have hc : ((k : ℕ) : R) = ((j : ℕ) : R) + ((k - j : ℕ) : R) := by
    have : j + (k - j) = k := by omega
    exact_mod_cast congrArg (Nat.cast : ℕ → R) this.symm
  rw [hc]; ring

/-- The coefficient in the rising-factorial derivative identity. -/
def dcoef (k j : ℕ) : ℕ := k.choose j * (k - 1 - j).factorial

/-- The Pascal-with-factorials step behind `derivative_rising`. -/
lemma dcoef_step (m j : ℕ) (hj : j ≤ m) :
    (if j = 0 then 0 else dcoef m (j - 1)) + dcoef m j * (m - j)
      + (if j = m then 1 else 0) = dcoef (m + 1) j := by
  rcases Nat.eq_zero_or_pos j with rfl | hjpos
  · -- j = 0
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [dcoef]
    · rw [if_pos rfl, if_neg (by omega), Nat.add_zero, Nat.zero_add, dcoef, dcoef]
      obtain ⟨t, rfl⟩ : ∃ t, m = t + 1 := ⟨m - 1, by omega⟩
      simp [Nat.factorial_succ, Nat.mul_comm]
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  rw [if_neg (by omega)]
  simp only [Nat.add_sub_cancel]
  rcases eq_or_lt_of_le hj with heq | hlt
  · -- i + 1 = m
    subst heq
    rw [if_pos rfl, Nat.sub_self, Nat.mul_zero, Nat.add_zero, dcoef, dcoef]
    simp [Nat.choose_succ_self_right]
  · -- i + 1 < m
    rw [if_neg (by omega), Nat.add_zero, dcoef, dcoef, dcoef]
    obtain ⟨t, ht⟩ : ∃ t, m - (i + 1) = t + 1 := ⟨m - (i + 1) - 1, by omega⟩
    have e1 : m - 1 - i = t + 1 := by omega
    have e2 : m - 1 - (i + 1) = t := by omega
    have e3 : m + 1 - 1 - (i + 1) = t + 1 := by omega
    rw [e1, e2, e3, ht, Nat.factorial_succ, Nat.choose_succ_succ' m i]
    ring

/-- The algebraic step behind the derivative identity, over any commutative ring. -/
lemma dcoef_sum_step (a : R) (m : ℕ) :
    (∑ j ∈ range m, ((dcoef m j : ℕ) : R) * rising a j) * (a + (m : R)) + rising a m
      = ∑ j ∈ range (m + 1), ((dcoef (m + 1) j : ℕ) : R) * rising a j := by
  rw [Finset.sum_mul]
  have step : ∀ i ∈ range m,
      ((dcoef m i : ℕ) : R) * rising a i * (a + (m : R))
        = ((dcoef m i : ℕ) : R) * rising a (i + 1)
          + ((dcoef m i * (m - i) : ℕ) : R) * rising a i := by
    intro i hi
    rw [mul_assoc, rising_mul_shift a i m (le_of_lt (mem_range.mp hi))]
    push_cast
    ring
  rw [Finset.sum_congr rfl step, Finset.sum_add_distrib]
  have A1 : ∑ i ∈ range m, ((dcoef m i : ℕ) : R) * rising a (i + 1)
      = ∑ j ∈ range (m + 1),
          ((if j = 0 then 0 else dcoef m (j - 1) : ℕ) : R) * rising a j := by
    rw [Finset.sum_range_succ']
    simp
  have A2 : ∑ i ∈ range m, ((dcoef m i * (m - i) : ℕ) : R) * rising a i
      = ∑ j ∈ range (m + 1), ((dcoef m j * (m - j) : ℕ) : R) * rising a j := by
    rw [Finset.sum_range_succ]
    simp
  have A3 : rising a m
      = ∑ j ∈ range (m + 1), ((if j = m then 1 else 0 : ℕ) : R) * rising a j := by
    rw [Finset.sum_range_succ]
    simp
  rw [A1, A2, A3, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hjm : j ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hj)
  rw [← dcoef_step m j hjm]
  push_cast
  ring

/-- **The chain-rule form of the derivative identity.**  Stated for an arbitrary inner
polynomial `u`, so it covers both `u = X + C a` (derivative `1`) and `u = C b - X`
(derivative `-1`) — the two substitutions Lemma 2 needs along `A = x+t`, `B = x+c-t`. -/
theorem derivative_rising_comp (u : R[X]) (k : ℕ) :
    derivative (rising u k)
      = derivative u * ∑ j ∈ range k, ((dcoef k j : ℕ) : R[X]) * rising u j := by
  induction k with
  | zero => simp
  | succ m ih =>
    rw [rising_succ, derivative_mul, ih, derivative_add, derivative_natCast, add_zero]
    rw [← dcoef_sum_step u m]
    ring

/-- **`d/dA (A)_k = ∑_{j<k} C(k,j)(k-1-j)!(A)_j`** — the write-up's
`∑_{s=1}^k C(k,s)(s-1)!(A)_{k-s}`, reindexed by `j = k - s` so the summation
variable carries no ℕ-subtraction.  The `u = X` case of the chain-rule form. -/
theorem derivative_rising (k : ℕ) :
    derivative (rising (X : R[X]) k) = ∑ j ∈ range k, ((dcoef k j : ℕ) : R[X]) * rising X j := by
  rw [derivative_rising_comp, derivative_X, one_mul]


/-- The rising factorial splits: `(a)_{j+i} = (a)_j (a+j)_i`. -/
lemma rising_add (a : R) (j i : ℕ) :
    rising a (j + i) = rising a j * rising (a + (j : R)) i := by
  unfold rising
  rw [Finset.prod_range_add]
  congr 1
  refine Finset.prod_congr rfl (fun t _ => ?_)
  push_cast
  ring

/-- The divided difference of two rising factorials, defined by the telescoping
recursion it satisfies.  Built only from `b + m` and `(a)_m`, so it inherits their
nonnegativity of coefficients. -/
def ddiff (a b : R) : ℕ → R
  | 0 => 0
  | m + 1 => ddiff a b m * (b + (m : R)) + rising a m

/-- **The divided difference.**  `(b)_m - (a)_m = (b - a) · ddiff a b m`. -/
theorem rising_sub_rising (a b : R) (m : ℕ) :
    rising b m - rising a m = (b - a) * ddiff a b m := by
  induction m with
  | zero => simp [ddiff]
  | succ t ih =>
    rw [rising_succ, rising_succ, ddiff]
    have : rising b t * (b + (t : R)) - rising a t * (a + (t : R))
        = (rising b t - rising a t) * (b + (t : R)) + rising a t * (b - a) := by ring
    rw [this, ih]
    ring

/-- **The bracket factorisation.**  With `N = 2k + m`,
`(A)_k(B)_{N-k} - (A)_{N-k}(B)_k = (A)_k(B)_k[(B+k)_m - (A+k)_m]`. -/
theorem bracket_factor (A B : R) (k m : ℕ) :
    rising A k * rising B (k + m) - rising A (k + m) * rising B k
      = rising A k * rising B k * (rising (B + (k : R)) m - rising (A + (k : R)) m) := by
  rw [rising_add B k m, rising_add A k m]
  ring

/-- Both steps together: the bracket carries an explicit factor of `B - A`. -/
theorem bracket_factor_sub (A B : R) (k m : ℕ) :
    rising A k * rising B (k + m) - rising A (k + m) * rising B k
      = (B - A) * (rising A k * rising B k * ddiff (A + (k : R)) (B + (k : R)) m) := by
  rw [bracket_factor, rising_sub_rising]
  ring

end Ring

section Swap

variable {M : Type*} [AddCommGroup M]

/-- **The reflection cancellation.**  If two index sets on `antidiagonal N` are each
other's image under `(k,m) ↦ (m,k)`, the common part of the two sums cancels and what
survives is a sum of antisymmetrised terms over the single-sided difference. -/
theorem sum_sub_sum_swap (N : ℕ) (g : ℕ × ℕ → M) (P : ℕ × ℕ → Prop) [DecidablePred P] :
    (∑ p ∈ (antidiagonal N).filter P, g p)
        - ∑ p ∈ (antidiagonal N).filter (fun p => P (Prod.swap p)), g p
      = ∑ p ∈ (antidiagonal N).filter (fun p => P p ∧ ¬ P (Prod.swap p)),
          (g p - g (Prod.swap p)) := by
  classical
  set S1 := (antidiagonal N).filter P with hS1
  set S2 := (antidiagonal N).filter (fun p => P (Prod.swap p)) with hS2
  set D := (antidiagonal N).filter (fun p => P p ∧ ¬ P (Prod.swap p)) with hD
  set E := (antidiagonal N).filter (fun p => P (Prod.swap p) ∧ ¬ P p) with hE
  -- split each sum into the common part and its own difference
  have h1 : ∑ p ∈ S1, g p = ∑ p ∈ (S1 ∩ S2), g p + ∑ p ∈ D, g p := by
    rw [← Finset.sum_union (by
      simp only [hS1, hS2, hD, Finset.disjoint_left, Finset.mem_inter, Finset.mem_filter]
      grind)]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext p
    simp only [hS1, hS2, hD, Finset.mem_union, Finset.mem_inter, Finset.mem_filter]
    grind
  have h2 : ∑ p ∈ S2, g p = ∑ p ∈ (S1 ∩ S2), g p + ∑ p ∈ E, g p := by
    rw [← Finset.sum_union (by
      simp only [hS1, hS2, hE, Finset.disjoint_left, Finset.mem_inter, Finset.mem_filter]
      grind)]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext p
    simp only [hS1, hS2, hE, Finset.mem_union, Finset.mem_inter, Finset.mem_filter]
    grind
  -- `E` is the swap image of `D`
  have h3 : ∑ p ∈ E, g p = ∑ p ∈ D, g (Prod.swap p) := by
    refine (Finset.sum_nbij' Prod.swap Prod.swap ?_ ?_ ?_ ?_ ?_).symm
    · intro p hp
      simp only [hD, hE, Finset.mem_filter, Finset.mem_antidiagonal,
        Prod.fst_swap, Prod.snd_swap, Prod.swap_swap] at hp ⊢
      exact ⟨by omega, hp.2.1, hp.2.2⟩
    · intro p hp
      simp only [hD, hE, Finset.mem_filter, Finset.mem_antidiagonal,
        Prod.fst_swap, Prod.snd_swap, Prod.swap_swap] at hp ⊢
      exact ⟨by omega, hp.2.1, hp.2.2⟩
    · intro p _; exact Prod.swap_swap p
    · intro p _; exact Prod.swap_swap p
    · intro p _; rfl
  rw [h1, h2, h3, Finset.sum_sub_distrib]
  abel

/-- **The write-up's boundary equation, in its index-only form.**  With `L ≤ r`, the two
one-sided constraints differ exactly on `L ≤ k < r` (equivalently `L ≤ k ≤ min(r-1, N-r)`,
since `r ≤ m` and `k + m = N`), and there the two sums contribute antisymmetrically. -/
theorem sum_sub_sum_swap_range (N r L : ℕ) (hL : L ≤ r) (g : ℕ × ℕ → M) :
    (∑ p ∈ (antidiagonal N).filter (fun p => L ≤ p.1 ∧ r ≤ p.2), g p)
        - ∑ p ∈ (antidiagonal N).filter (fun p => r ≤ p.1 ∧ L ≤ p.2), g p
      = ∑ p ∈ (antidiagonal N).filter (fun p => L ≤ p.1 ∧ p.1 < r ∧ r ≤ p.2),
          (g p - g (Prod.swap p)) := by
  classical
  have hswap : ((antidiagonal N).filter (fun p => r ≤ p.1 ∧ L ≤ p.2))
      = (antidiagonal N).filter (fun p => L ≤ (Prod.swap p).1 ∧ r ≤ (Prod.swap p).2) := by
    apply Finset.filter_congr
    intro p _
    simp only [Prod.fst_swap, Prod.snd_swap]
    constructor <;> (intro h; exact ⟨h.2, h.1⟩)
  rw [hswap, sum_sub_sum_swap N g (fun p => L ≤ p.1 ∧ r ≤ p.2)]
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  apply Finset.filter_congr
  intro p hp
  have hsum : p.1 + p.2 = N := by simpa using hp
  simp only [Prod.fst_swap, Prod.snd_swap]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, by omega, h2⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h3⟩, by omega⟩

end Swap

section Reindex

variable {M : Type*} [AddCommMonoid M]

/-- Reindex `range k` as `Icc 1 k` by `s ↦ k - s`. -/
lemma sum_range_eq_sum_Icc (k : ℕ) (g : ℕ → M) :
    ∑ j ∈ range k, g j = ∑ s ∈ Finset.Icc 1 k, g (k - s) := by
  refine Finset.sum_nbij' (fun j => k - j) (fun s => k - s) ?_ ?_ ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_range] at hj
    simp only [Finset.mem_Icc]
    omega
  · intro s hs
    simp only [Finset.mem_Icc] at hs
    simp only [Finset.mem_range]
    omega
  · intro j hj
    simp only [Finset.mem_range] at hj
    omega
  · intro s hs
    simp only [Finset.mem_Icc] at hs
    omega
  · intro j hj
    simp only [Finset.mem_range] at hj
    congr 1
    omega

/-- Swap a sum over pairs `(p, s)` with `s ≤ p.1` into `s` outermost. -/
lemma sum_swap_shift (n : ℕ) (F : Finset (ℕ × ℕ)) (hF : ∀ p ∈ F, p.1 ≤ n)
    (h : ℕ × ℕ → ℕ → M) :
    ∑ p ∈ F, ∑ s ∈ Finset.Icc 1 p.1, h p s
      = ∑ s ∈ Finset.Icc 1 n, ∑ p ∈ F.filter (fun p => s ≤ p.1), h p s := by
  rw [Finset.sum_comm' (t' := Finset.Icc 1 n) (s' := fun s => F.filter (fun p => s ≤ p.1))]
  intro p s
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨hp, h1, h2⟩
    exact ⟨⟨hp, h2⟩, h1, le_trans h2 (hF p hp)⟩
  · rintro ⟨⟨hp, h2⟩, h1, -⟩
    exact ⟨hp, h1, h2⟩

/-- Shift the first index down by `s`, moving from `antidiagonal n` to `antidiagonal (n-s)`. -/
lemma sum_shift_antidiagonal (n s : ℕ) (P : ℕ × ℕ → Prop) [DecidablePred P]
    (g : ℕ × ℕ → M) :
    ∑ p ∈ ((antidiagonal n).filter P).filter (fun p => s ≤ p.1), g (p.1 - s, p.2)
      = ∑ q ∈ (antidiagonal (n - s)).filter (fun q => P (q.1 + s, q.2) ∧ s ≤ n), g q := by
  refine Finset.sum_nbij' (fun p => (p.1 - s, p.2)) (fun q => (q.1 + s, q.2)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_antidiagonal] at hp ⊢
    obtain ⟨⟨hsum, hP⟩, hs⟩ := hp
    refine ⟨by omega, ?_, by omega⟩
    rw [show p.1 - s + s = p.1 from by omega]
    simpa using hP
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_antidiagonal] at hq ⊢
    obtain ⟨hsum, hP, hs⟩ := hq
    exact ⟨⟨by omega, hP⟩, by omega⟩
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_antidiagonal] at hp
    have : p.1 - s + s = p.1 := by omega
    simp [this]
  · intro q hq
    simp
  · intro p _; rfl


/-- Reindex a filtered antidiagonal sum by `(k,m) ↦ (m,k)`. -/
lemma sum_antidiagonal_swap (n : ℕ) (P : ℕ × ℕ → Prop) [DecidablePred P] (f : ℕ × ℕ → M) :
    ∑ p ∈ (antidiagonal n).filter P, f p
      = ∑ p ∈ (antidiagonal n).filter (fun p => P (Prod.swap p)), f (Prod.swap p) := by
  refine Finset.sum_nbij' Prod.swap Prod.swap ?_ ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_antidiagonal, Prod.swap_swap,
      Prod.fst_swap, Prod.snd_swap] at hp ⊢
    exact ⟨by omega, hp.2⟩
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_antidiagonal,
      Prod.fst_swap, Prod.snd_swap] at hp ⊢
    exact ⟨by omega, hp.2⟩
  · intro p _; exact Prod.swap_swap p
  · intro p _; exact Prod.swap_swap p
  · intro p _; rfl

end Reindex

section Assemble

variable {R : Type*} [CommRing R]

/-- **`T_A(s) - T_B(s) = (B - A) · R_s`, with `R_s` explicit.**  This is where the two
halves meet: the reflection cancellation reduces the difference of the two one-sided sums
to antisymmetrised terms on `L ≤ k < r`, and the bracket factorisation extracts `B - A`
from each of them.  What is left is a single sum whose summand is built from binomials,
rising factorials and `ddiff` — every factor manifestly free of subtraction. -/
theorem sum_filter_sub_swap_factor (N r L : ℕ) (hL : L ≤ r) (A B : R) :
    (∑ p ∈ (antidiagonal N).filter (fun p => L ≤ p.1 ∧ r ≤ p.2),
        (N.choose p.1 : R) * (rising A p.1 * rising B p.2))
      - ∑ p ∈ (antidiagonal N).filter (fun p => r ≤ p.1 ∧ L ≤ p.2),
        (N.choose p.1 : R) * (rising A p.1 * rising B p.2)
      = (B - A) * ∑ p ∈ (antidiagonal N).filter (fun p => L ≤ p.1 ∧ p.1 < r ∧ r ≤ p.2),
          (N.choose p.1 : R) * (rising A p.1 * rising B p.1
            * ddiff (A + (p.1 : R)) (B + (p.1 : R)) (p.2 - p.1)) := by
  rw [sum_sub_sum_swap_range N r L hL
    (fun p => (N.choose p.1 : R) * (rising A p.1 * rising B p.2)), Finset.mul_sum]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  obtain ⟨k, j⟩ := p
  simp only [Finset.mem_filter, Finset.mem_antidiagonal] at hp
  obtain ⟨m, rfl⟩ : ∃ m, j = k + m := ⟨j - k, by omega⟩
  have hch : N.choose (k + m) = N.choose k := Nat.choose_symm_of_eq_add (by omega)
  simp only [Prod.fst_swap, Prod.snd_swap, hch, Nat.add_sub_cancel_left]
  rw [← mul_sub, bracket_factor_sub A B k m]
  ring


/-- **The reindex behind the `∂_A` decomposition**, as a pure sum identity over any
commutative ring: no derivatives, and the second index rides along in an arbitrary `G`.
Collecting by `s = k - j` turns one sum over `antidiagonal n` into a sum over `s` of sums
over `antidiagonal (n-s)` carrying the write-up's `C(n,s)(s-1)!` weights.  The binomial
bookkeeping is `Nat.choose_mul`: `C(n,k)C(k,s) = C(n,s)C(n-s,k-s)`. -/
theorem sum_dcoef_reindex (n : ℕ) (P : ℕ × ℕ → Prop) [DecidablePred P] (u : R) (G : ℕ → R) :
    ∑ p ∈ (antidiagonal n).filter P, ((n.choose p.1 : ℕ) : R) *
        ((∑ j ∈ range p.1, ((dcoef p.1 j : ℕ) : R) * rising u j) * G p.2)
      = ∑ s ∈ Finset.Icc 1 n, ((n.choose s * (s - 1).factorial : ℕ) : R) *
          ∑ q ∈ (antidiagonal (n - s)).filter (fun q => P (q.1 + s, q.2) ∧ s ≤ n),
            (((n - s).choose q.1 : ℕ) : R) * (rising u q.1 * G q.2) := by
  have h1 : ∀ p ∈ (antidiagonal n).filter P,
      ((n.choose p.1 : ℕ) : R) *
          ((∑ j ∈ range p.1, ((dcoef p.1 j : ℕ) : R) * rising u j) * G p.2)
        = ∑ s ∈ Finset.Icc 1 p.1, ((n.choose s * (s - 1).factorial : ℕ) : R)
            * ((((n - s).choose (p.1 - s) : ℕ) : R) * (rising u (p.1 - s) * G p.2)) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_antidiagonal] at hp
    rw [Finset.sum_mul, Finset.mul_sum, sum_range_eq_sum_Icc]
    refine Finset.sum_congr rfl (fun s hs => ?_)
    simp only [Finset.mem_Icc] at hs
    have hd : dcoef p.1 (p.1 - s) = p.1.choose s * (s - 1).factorial := by
      rw [dcoef, show p.1 - 1 - (p.1 - s) = s - 1 from by omega,
        ← Nat.choose_symm (by omega : p.1 - s ≤ p.1),
        show p.1 - (p.1 - s) = s from by omega]
    rw [hd]
    have hb : n.choose p.1 * p.1.choose s = n.choose s * ((n - s).choose (p.1 - s)) :=
      Nat.choose_mul (by omega)
    have hbc : ((n.choose p.1 : ℕ) : R) * ((p.1.choose s : ℕ) : R)
        = ((n.choose s : ℕ) : R) * (((n - s).choose (p.1 - s) : ℕ) : R) := by
      exact_mod_cast congrArg (fun t : ℕ => (t : R)) hb
    push_cast
    linear_combination (((s - 1).factorial : ℕ) : R) * rising u (p.1 - s) * G p.2 * hbc
  rw [Finset.sum_congr rfl h1,
    sum_swap_shift n ((antidiagonal n).filter P) (fun p hp => by
      simp only [Finset.mem_filter, Finset.mem_antidiagonal] at hp; omega)]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [Finset.mul_sum, ← sum_shift_antidiagonal n s P
    (fun q => ((n.choose s * (s - 1).factorial : ℕ) : R) *
      ((((n - s).choose q.1 : ℕ) : R) * (rising u q.1 * G q.2)))]

/-- **The `∂_A` decomposition.**  Differentiating the truncation in its first argument,
where the inner polynomial `v` is arbitrary (so this covers `v = X + C a` as well as
`v = X`) and the second factor `G` is arbitrary (so it need not be constant in the
variable being differentiated). -/
theorem derivative_trunc (n : ℕ) (P : ℕ × ℕ → Prop) [DecidablePred P] (v : R[X])
    (G : ℕ → R[X]) :
    ∑ p ∈ (antidiagonal n).filter P,
        ((n.choose p.1 : ℕ) : R[X]) * (derivative (rising v p.1) * G p.2)
      = derivative v * ∑ s ∈ Finset.Icc 1 n, ((n.choose s * (s - 1).factorial : ℕ) : R[X]) *
          ∑ q ∈ (antidiagonal (n - s)).filter (fun q => P (q.1 + s, q.2) ∧ s ≤ n),
            (((n - s).choose q.1 : ℕ) : R[X]) * (rising v q.1 * G q.2) := by
  rw [← sum_dcoef_reindex n P v G, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [derivative_rising_comp]
  ring


/-- **The `∂_B` mirror.**  Obtained from `derivative_trunc` by the `(k,m) ↦ (m,k)`
reindex rather than by repeating the argument. -/
theorem derivative_trunc_snd (n : ℕ) (P : ℕ × ℕ → Prop) [DecidablePred P] (w : R[X])
    (H : ℕ → R[X]) :
    ∑ p ∈ (antidiagonal n).filter P,
        ((n.choose p.1 : ℕ) : R[X]) * (H p.1 * derivative (rising w p.2))
      = derivative w * ∑ s ∈ Finset.Icc 1 n, ((n.choose s * (s - 1).factorial : ℕ) : R[X]) *
          ∑ q ∈ (antidiagonal (n - s)).filter (fun q => P (q.2, q.1 + s) ∧ s ≤ n),
            (((n - s).choose q.1 : ℕ) : R[X]) * (rising w q.1 * H q.2) := by
  have hfil : ∀ s : ℕ,
      (antidiagonal (n - s)).filter (fun q => P (q.2, q.1 + s) ∧ s ≤ n)
        = (antidiagonal (n - s)).filter (fun q => P (Prod.swap (q.1 + s, q.2)) ∧ s ≤ n) :=
    fun s => Finset.filter_congr (fun q _ => Iff.rfl)
  simp only [hfil]
  rw [sum_antidiagonal_swap n P
    (fun p => ((n.choose p.1 : ℕ) : R[X]) * (H p.1 * derivative (rising w p.2)))]
  rw [← derivative_trunc n (fun p => P (Prod.swap p)) w H]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  simp only [Finset.mem_filter, Finset.mem_antidiagonal, Prod.fst_swap, Prod.snd_swap] at hp ⊢
  have hch : n.choose p.2 = n.choose p.1 := Nat.choose_symm_of_eq_add (by omega)
  rw [hch]
  ring

/-- **The product rule for the truncation.**  Both arguments vary, so the derivative
splits into an `A`-part and a `B`-part, each an `s`-decomposition. -/
theorem derivative_trunc_prod (n : ℕ) (P : ℕ × ℕ → Prop) [DecidablePred P] (v w : R[X]) :
    derivative (∑ p ∈ (antidiagonal n).filter P,
        ((n.choose p.1 : ℕ) : R[X]) * (rising v p.1 * rising w p.2))
      = derivative v * (∑ s ∈ Finset.Icc 1 n,
            ((n.choose s * (s - 1).factorial : ℕ) : R[X]) *
            ∑ q ∈ (antidiagonal (n - s)).filter (fun q => P (q.1 + s, q.2) ∧ s ≤ n),
              (((n - s).choose q.1 : ℕ) : R[X]) * (rising v q.1 * rising w q.2))
        + derivative w * (∑ s ∈ Finset.Icc 1 n,
            ((n.choose s * (s - 1).factorial : ℕ) : R[X]) *
            ∑ q ∈ (antidiagonal (n - s)).filter (fun q => P (q.2, q.1 + s) ∧ s ≤ n),
              (((n - s).choose q.1 : ℕ) : R[X]) * (rising w q.1 * rising v q.2)) := by
  rw [derivative_sum, ← derivative_trunc n P v (fun j => rising w j),
    ← derivative_trunc_snd n P w (fun j => rising v j), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [derivative_mul, derivative_natCast, zero_mul, zero_add, derivative_mul]
  ring


/-! ### The balancing line

`trunc n r A B` is the central truncation as a function of its two arguments, so that
`V n r α β` is the difference of its values at `(x+α, x+β)` and `(x+α+β, x)` — two points
with the same sum.  `Rfun` is the explicit quotient that `sum_filter_sub_swap_factor`
produces, assembled over `s`. -/

/-- The central truncation of `C_{n,r}` at a general pair of arguments. -/
noncomputable def trunc (n r : ℕ) (A B : R) : R :=
  ∑ p ∈ (antidiagonal n).filter (fun p => r ≤ p.1 ∧ r ≤ p.2),
    ((n.choose p.1 : ℕ) : R) * (rising A p.1 * rising B p.2)

/-- The explicit `R_{n,r}`: every factor is a binomial, a rising factorial, or `ddiff`. -/
noncomputable def Rfun (n r : ℕ) (A B : R) : R :=
  ∑ s ∈ Finset.Icc 1 n, ((n.choose s * (s - 1).factorial : ℕ) : R) *
    ∑ q ∈ (antidiagonal (n - s)).filter (fun q => r - s ≤ q.1 ∧ q.1 < r ∧ r ≤ q.2),
      (((n - s).choose q.1 : ℕ) : R) * (rising A q.1 * rising B q.1 *
        ddiff (A + (q.1 : R)) (B + (q.1 : R)) (q.2 - q.1))


/-- The per-`s` step: after one swap the two inner sums are exactly the pair that
`sum_filter_sub_swap_factor` takes, with `L = r - s`. -/
lemma inner_sub (n s N r : ℕ) (hs : s ≤ n) (a b : R) :
    (∑ q ∈ (antidiagonal N).filter (fun q => (r ≤ q.1 + s ∧ r ≤ q.2) ∧ s ≤ n),
        ((N.choose q.1 : ℕ) : R) * (rising a q.1 * rising b q.2))
      - ∑ q ∈ (antidiagonal N).filter (fun q => (r ≤ q.2 ∧ r ≤ q.1 + s) ∧ s ≤ n),
        ((N.choose q.1 : ℕ) : R) * (rising b q.1 * rising a q.2)
      = (b - a) * ∑ q ∈ (antidiagonal N).filter (fun q => r - s ≤ q.1 ∧ q.1 < r ∧ r ≤ q.2),
          ((N.choose q.1 : ℕ) : R) * (rising a q.1 * rising b q.1 *
            ddiff (a + (q.1 : R)) (b + (q.1 : R)) (q.2 - q.1)) := by
  have hA : (antidiagonal N).filter (fun q => (r ≤ q.1 + s ∧ r ≤ q.2) ∧ s ≤ n)
      = (antidiagonal N).filter (fun q => r - s ≤ q.1 ∧ r ≤ q.2) := by
    apply Finset.filter_congr
    intro q _
    constructor
    · rintro ⟨⟨h1, h2⟩, -⟩; exact ⟨by omega, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨by omega, h2⟩, hs⟩
  have hB : ∑ q ∈ (antidiagonal N).filter (fun q => (r ≤ q.2 ∧ r ≤ q.1 + s) ∧ s ≤ n),
        ((N.choose q.1 : ℕ) : R) * (rising b q.1 * rising a q.2)
      = ∑ q ∈ (antidiagonal N).filter (fun q => r ≤ q.1 ∧ r - s ≤ q.2),
        ((N.choose q.1 : ℕ) : R) * (rising a q.1 * rising b q.2) := by
    rw [sum_antidiagonal_swap N _
      (fun q => ((N.choose q.1 : ℕ) : R) * (rising b q.1 * rising a q.2))]
    have hset : (antidiagonal N).filter
          (fun q => ((r ≤ (Prod.swap q).2 ∧ r ≤ (Prod.swap q).1 + s) ∧ s ≤ n))
        = (antidiagonal N).filter (fun q => r ≤ q.1 ∧ r - s ≤ q.2) := by
      apply Finset.filter_congr
      intro q _
      simp only [Prod.fst_swap, Prod.snd_swap]
      constructor
      · rintro ⟨⟨h1, h2⟩, -⟩; exact ⟨h1, by omega⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨h1, by omega⟩, hs⟩
    rw [hset]
    refine Finset.sum_congr rfl (fun q hq => ?_)
    simp only [Finset.mem_filter, Finset.mem_antidiagonal] at hq
    have hch : N.choose q.2 = N.choose q.1 := Nat.choose_symm_of_eq_add (by omega)
    simp only [Prod.fst_swap, Prod.snd_swap, hch]
    ring
  rw [hA, hB, sum_filter_sub_swap_factor N r (r - s) (by omega) a b]


/-- **Lemma 1, assembled.**  Along any line on which the two arguments move at opposite
unit rates — which is what `A = x+t`, `B = x+c-t` does — the derivative of the truncation
carries an explicit factor `B - A`, with the quotient `Rfun` built only from binomials,
rising factorials and `ddiff`.  Substituting `A = x+t`, `B = x+c-t` makes `B - A = c-2t`,
the sign factor Lemma 2 integrates against. -/
theorem derivative_trunc_line (n r : ℕ) (a b : R[X])
    (ha : derivative a = 1) (hb : derivative b = -1) :
    derivative (trunc n r a b) = (b - a) * Rfun n r a b := by
  rw [trunc, derivative_trunc_prod, ha, hb, one_mul, neg_one_mul, ← sub_eq_add_neg,
    Rfun, ← Finset.sum_sub_distrib]
  conv_rhs => rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun s hs => ?_)
  simp only [Finset.mem_Icc] at hs
  rw [← mul_sub, inner_sub n s (n - s) r (by omega) a b]
  ring


/-- The truncation is symmetric in its two arguments: the filter is symmetric and
`C(n,k) = C(n,m)` on the antidiagonal. -/
lemma trunc_symm (n r : ℕ) (A B : R) : trunc n r A B = trunc n r B A := by
  rw [trunc, trunc, sum_antidiagonal_swap n (fun p => r ≤ p.1 ∧ r ≤ p.2)
    (fun p => ((n.choose p.1 : ℕ) : R) * (rising A p.1 * rising B p.2))]
  have hset : (antidiagonal n).filter
        (fun p => r ≤ (Prod.swap p).1 ∧ r ≤ (Prod.swap p).2)
      = (antidiagonal n).filter (fun p => r ≤ p.1 ∧ r ≤ p.2) := by
    apply Finset.filter_congr
    intro q _
    simp only [Prod.fst_swap, Prod.snd_swap]
    exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  rw [hset]
  refine Finset.sum_congr rfl (fun q hq => ?_)
  simp only [Finset.mem_filter, Finset.mem_antidiagonal] at hq
  have hch : n.choose q.2 = n.choose q.1 := Nat.choose_symm_of_eq_add (by omega)
  simp only [Prod.fst_swap, Prod.snd_swap, hch]
  ring

end Assemble

section Map

/-! ### Everything commutes with a ring hom

`rising`, `ddiff`, `trunc` and `Rfun` are built from `+`, `*` and `ℕ`-casts, so a
ring hom passes straight through.  Instantiating at `Polynomial.evalRingHom (C t)` is
what moves a statement in `ℝ[x][t]` down to `ℝ[x]` at a fixed `t`. -/

variable {R S : Type*} [CommRing R] [CommRing S]

lemma rising_map (f : R →+* S) (a : R) (k : ℕ) : f (rising a k) = rising (f a) k := by
  unfold rising
  rw [map_prod]
  exact Finset.prod_congr rfl (fun i _ => by rw [map_add, map_natCast])

lemma ddiff_map (f : R →+* S) (a b : R) (m : ℕ) :
    f (ddiff a b m) = ddiff (f a) (f b) m := by
  induction m with
  | zero => rw [ddiff, ddiff, map_zero]
  | succ t ih =>
    rw [ddiff, ddiff, map_add, map_mul, ih, map_add, map_natCast, rising_map]

lemma trunc_map (f : R →+* S) (n r : ℕ) (A B : R) :
    f (trunc n r A B) = trunc n r (f A) (f B) := by
  unfold trunc
  rw [map_sum]
  exact Finset.sum_congr rfl (fun p _ => by
    rw [map_mul, map_natCast, map_mul, rising_map, rising_map])

lemma Rfun_map (f : R →+* S) (n r : ℕ) (A B : R) :
    f (Rfun n r A B) = Rfun n r (f A) (f B) := by
  unfold Rfun
  rw [map_sum]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [map_mul, map_natCast, map_sum]
  refine congrArg _ (Finset.sum_congr rfl (fun q _ => ?_))
  rw [map_mul, map_natCast, map_mul, map_mul, rising_map, rising_map, ddiff_map,
    map_add, map_natCast, map_add, map_natCast]

end Map

section Line

/-! ### The balancing line in `ℝ[x][t]` -/

/-- `x + t`, as an element of `ℝ[x][t]`. -/
noncomputable def aLine : (ℝ[X])[X] := Polynomial.C (Polynomial.X : ℝ[X]) + Polynomial.X

/-- `(x + c) - t`, as an element of `ℝ[x][t]`. -/
noncomputable def bLine (c : ℝ) : (ℝ[X])[X] :=
  Polynomial.C ((Polynomial.X : ℝ[X]) + Polynomial.C c) - Polynomial.X

lemma derivative_aLine : derivative aLine = 1 := by
  rw [aLine, derivative_add, Polynomial.derivative_C, Polynomial.derivative_X, zero_add]

lemma derivative_bLine (c : ℝ) : derivative (bLine c) = -1 := by
  rw [bLine, derivative_sub, Polynomial.derivative_C, Polynomial.derivative_X, zero_sub]

lemma eval_aLine (t : ℝ) :
    aLine.eval (Polynomial.C t) = Polynomial.X + Polynomial.C t := by
  simp [aLine]

lemma eval_bLine (c t : ℝ) :
    (bLine c).eval (Polynomial.C t) = Polynomial.X + Polynomial.C (c - t) := by
  simp [bLine, Polynomial.C_sub]
  ring

lemma eval_trunc_line (n r : ℕ) (c t : ℝ) :
    (trunc n r aLine (bLine c)).eval (Polynomial.C t)
      = trunc n r (Polynomial.X + Polynomial.C t)
          (Polynomial.X + Polynomial.C (c - t)) := by
  have h := trunc_map (Polynomial.evalRingHom (Polynomial.C t : ℝ[X])) n r aLine (bLine c)
  simpa [Polynomial.coe_evalRingHom, eval_aLine, eval_bLine] using h

lemma eval_Rfun_line (n r : ℕ) (c t : ℝ) :
    (Rfun n r aLine (bLine c)).eval (Polynomial.C t)
      = Rfun n r (Polynomial.X + Polynomial.C t)
          (Polynomial.X + Polynomial.C (c - t)) := by
  have h := Rfun_map (Polynomial.evalRingHom (Polynomial.C t : ℝ[X])) n r aLine (bLine c)
  simpa [Polynomial.coe_evalRingHom, eval_aLine, eval_bLine] using h

end Line

section Nonneg

/-! ### Nonnegative coefficients

`Rfun` was built only from binomials, rising factorials and `ddiff`, and `ddiff` was
defined by its recursion rather than by its coefficient expansion.  The payoff is here:
nonnegativity propagates through all of it by structural induction, with no `p_i ≥ 0`
side condition to establish separately. -/

/-- Every coefficient is nonnegative. -/
def NonnegCoeff (p : ℝ[X]) : Prop := ∀ j, 0 ≤ p.coeff j

lemma nonnegCoeff_zero : NonnegCoeff 0 := fun j => by simp

lemma nonnegCoeff_one : NonnegCoeff 1 := fun j => by
  rw [Polynomial.coeff_one]; split_ifs <;> norm_num

lemma nonnegCoeff_C {a : ℝ} (ha : 0 ≤ a) : NonnegCoeff (C a) := fun j => by
  rw [Polynomial.coeff_C]; split_ifs with h
  · exact ha
  · exact le_refl 0

lemma nonnegCoeff_X : NonnegCoeff (X : ℝ[X]) := fun j => by
  rw [Polynomial.coeff_X]; split_ifs <;> norm_num

lemma nonnegCoeff_natCast (m : ℕ) : NonnegCoeff ((m : ℕ) : ℝ[X]) := by
  rw [← Polynomial.C_eq_natCast]
  exact nonnegCoeff_C (by positivity)

lemma NonnegCoeff.add {p q : ℝ[X]} (hp : NonnegCoeff p) (hq : NonnegCoeff q) :
    NonnegCoeff (p + q) := fun j => by
  rw [Polynomial.coeff_add]; exact add_nonneg (hp j) (hq j)

lemma NonnegCoeff.mul {p q : ℝ[X]} (hp : NonnegCoeff p) (hq : NonnegCoeff q) :
    NonnegCoeff (p * q) := fun j => by
  rw [Polynomial.coeff_mul]
  exact Finset.sum_nonneg (fun ij _ => mul_nonneg (hp _) (hq _))

lemma NonnegCoeff.sum {ι : Type*} (s : Finset ι) (f : ι → ℝ[X])
    (h : ∀ i ∈ s, NonnegCoeff (f i)) : NonnegCoeff (∑ i ∈ s, f i) := fun j => by
  rw [Polynomial.finsetSum_coeff]
  exact Finset.sum_nonneg (fun i hi => h i hi j)

lemma nonnegCoeff_X_add_C {a : ℝ} (ha : 0 ≤ a) : NonnegCoeff (X + C a) :=
  nonnegCoeff_X.add (nonnegCoeff_C ha)

lemma nonnegCoeff_rising {a : ℝ[X]} (ha : NonnegCoeff a) (k : ℕ) :
    NonnegCoeff (rising a k) := by
  induction k with
  | zero => rw [rising_zero]; exact nonnegCoeff_one
  | succ m ih => rw [rising_succ]; exact ih.mul (ha.add (nonnegCoeff_natCast m))

lemma nonnegCoeff_ddiff {a b : ℝ[X]} (ha : NonnegCoeff a) (hb : NonnegCoeff b) (m : ℕ) :
    NonnegCoeff (ddiff a b m) := by
  induction m with
  | zero => rw [ddiff]; exact nonnegCoeff_zero
  | succ t ih =>
    rw [ddiff]
    exact (ih.mul (hb.add (nonnegCoeff_natCast t))).add (nonnegCoeff_rising ha t)

lemma nonnegCoeff_Rfun {A B : ℝ[X]} (hA : NonnegCoeff A) (hB : NonnegCoeff B) (n r : ℕ) :
    NonnegCoeff (Rfun n r A B) := by
  rw [Rfun]
  refine NonnegCoeff.sum _ _ (fun s _ => (nonnegCoeff_natCast _).mul
    (NonnegCoeff.sum _ _ (fun q _ => ?_)))
  exact (nonnegCoeff_natCast _).mul
    (((nonnegCoeff_rising hA _).mul (nonnegCoeff_rising hB _)).mul
      (nonnegCoeff_ddiff (hA.add (nonnegCoeff_natCast _)) (hB.add (nonnegCoeff_natCast _)) _))

/-- **The quotient is nonnegative along the balancing line.**  With `A = x + t` and
`B = x + (c-t)`, both arguments have nonnegative coefficients exactly when `0 ≤ t` and
`t ≤ c`, which is the range Lemma 2 integrates over. -/
theorem nonnegCoeff_Rfun_line (n r : ℕ) {t u : ℝ} (ht : 0 ≤ t) (hu : 0 ≤ u) :
    NonnegCoeff (Rfun n r (X + C t) (X + C u)) :=
  nonnegCoeff_Rfun (nonnegCoeff_X_add_C ht) (nonnegCoeff_X_add_C hu) n r


/-! ### Strict positivity up to a degree

The write-up gets strictness from a single distinguished summand: at `s = 1` the inner
range collapses to `k = r-1`, and that term alone has strictly positive coefficients all
the way to degree `n-2`.  Everything else in `Rfun` is nonnegative, so it cannot cancel. -/

/-- Strictly positive in every coefficient up to degree `d`. -/
def PosUpTo (d : ℕ) (p : ℝ[X]) : Prop := ∀ j ≤ d, 0 < p.coeff j

lemma PosUpTo.mul {d e : ℕ} {p q : ℝ[X]} (hp : PosUpTo d p) (hpn : NonnegCoeff p)
    (hq : PosUpTo e q) (hqn : NonnegCoeff q) : PosUpTo (d + e) (p * q) := by
  intro j hj
  rw [Polynomial.coeff_mul]
  refine Finset.sum_pos' (fun ij _ => mul_nonneg (hpn _) (hqn _)) ⟨(min j d, j - min j d), ?_, ?_⟩
  · simp only [Finset.mem_antidiagonal]
    omega
  · exact mul_pos (hp _ (by omega)) (hq _ (by omega))

lemma PosUpTo.add_nonneg {d : ℕ} {p q : ℝ[X]} (hp : PosUpTo d p) (hq : NonnegCoeff q) :
    PosUpTo d (p + q) := fun j hj => by
  rw [Polynomial.coeff_add]
  exact add_pos_of_pos_of_nonneg (hp j hj) (hq j)

lemma posUpTo_one : PosUpTo 0 (1 : ℝ[X]) := by
  intro j hj
  interval_cases j
  simp

lemma posUpTo_X_add_C {a : ℝ} (ha : 0 < a) : PosUpTo 1 (X + C a) := by
  intro j hj
  interval_cases j
  · simpa using ha
  · simp

lemma posUpTo_X_add_C_natCast {t : ℝ} (ht : 0 < t) (m : ℕ) :
    PosUpTo 1 ((X + C t) + (m : ℝ[X])) := by
  have hEq : (X + C t) + (m : ℝ[X]) = X + C (t + (m : ℝ)) := by
    rw [Polynomial.C_add, ← Polynomial.C_eq_natCast]
    ring
  rw [hEq]
  exact posUpTo_X_add_C (by positivity)

lemma posUpTo_rising {t : ℝ} (ht : 0 < t) (k : ℕ) : PosUpTo k (rising (X + C t) k) := by
  induction k with
  | zero => rw [rising_zero]; exact posUpTo_one
  | succ m ih =>
    rw [rising_succ]
    exact ih.mul (nonnegCoeff_rising (nonnegCoeff_X_add_C ht.le) m)
      (posUpTo_X_add_C_natCast ht m)
      ((nonnegCoeff_X_add_C ht.le).add (nonnegCoeff_natCast m))

lemma coeff_natCast_zero (m : ℕ) : ((m : ℕ) : ℝ[X]).coeff 0 = (m : ℝ) := by
  rw [← Polynomial.C_eq_natCast, Polynomial.coeff_C_zero]

lemma coeff_natCast_ne_zero (m j : ℕ) (hj : j ≠ 0) : ((m : ℕ) : ℝ[X]).coeff j = 0 := by
  rw [← Polynomial.C_eq_natCast, Polynomial.coeff_C]
  simp [hj]

lemma posUpTo_ddiff {a b : ℝ[X]} (han : NonnegCoeff a) (hb : PosUpTo 1 b)
    (hbn : NonnegCoeff b) (m : ℕ) : PosUpTo m (ddiff a b (m + 1)) := by
  induction m with
  | zero =>
    rw [ddiff, ddiff, rising_zero, zero_mul, zero_add]
    exact posUpTo_one
  | succ t ih =>
    rw [ddiff]
    refine PosUpTo.add_nonneg ?_ (nonnegCoeff_rising han (t + 1))
    exact ih.mul (nonnegCoeff_ddiff han hbn (t + 1))
      (fun j hj => by
        rw [Polynomial.coeff_add]
        rcases Nat.eq_zero_or_pos j with rfl | hjp
        · rw [coeff_natCast_zero]
          have h0 := hb 0 (by omega)
          have hc : (0 : ℝ) ≤ ((t + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
          linarith
        · have hj1 : j = 1 := by omega
          subst hj1
          rw [coeff_natCast_ne_zero _ 1 one_ne_zero, add_zero]
          exact hb 1 (le_refl 1))
      ((hbn.add (nonnegCoeff_natCast (t + 1))))


lemma PosUpTo.natCast_mul {d k : ℕ} {q : ℝ[X]} (hk : 0 < k) (hq : PosUpTo d q) :
    PosUpTo d (((k : ℕ) : ℝ[X]) * q) := fun j hj => by
  rw [← Polynomial.C_eq_natCast, Polynomial.coeff_C_mul]
  exact mul_pos (by exact_mod_cast hk) (hq j hj)

/-- **The distinguished summand.**  At `s = 1` the inner range collapses to the single
pair `(r-1, n-r)`, and that term's three factors have degrees `r-1`, `r-1` and `n-2r`,
summing to exactly `n-2`.  Everything else in `Rfun` is nonnegative and cannot cancel. -/
theorem posUpTo_Rfun_line (n r : ℕ) (hr : 1 ≤ r) (hrn : 2 * r ≤ n)
    {t u : ℝ} (ht : 0 < t) (hu : 0 < u) :
    PosUpTo (n - 2) (Rfun n r (X + C t) (X + C u)) := by
  have h1mem : (1 : ℕ) ∈ Finset.Icc 1 n := by simp; omega
  rw [Rfun, ← Finset.add_sum_erase _ _ h1mem]
  refine PosUpTo.add_nonneg ?_ (NonnegCoeff.sum _ _ (fun s _ => ?_))
  · -- the `s = 1` term
    have hfil : (antidiagonal (n - 1)).filter (fun q => r - 1 ≤ q.1 ∧ q.1 < r ∧ r ≤ q.2)
        = {(r - 1, n - r)} := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_antidiagonal, Finset.mem_singleton,
        Prod.ext_iff]
      constructor
      · rintro ⟨hsum, ha, hb, hc⟩
        exact ⟨by omega, by omega⟩
      · rintro ⟨ha, hb⟩
        exact ⟨by omega, by omega, by omega, by omega⟩
    simp only [Nat.sub_self, hfil, Finset.sum_singleton]
    refine PosUpTo.natCast_mul (by simp [Nat.choose_one_right]; omega) ?_
    refine PosUpTo.natCast_mul (Nat.choose_pos (by omega)) ?_
    have hdeg : (r - 1) + (r - 1) + ((n - r) - (r - 1) - 1) = n - 2 := by omega
    rw [← hdeg]
    refine PosUpTo.mul ?_
      ((nonnegCoeff_rising (nonnegCoeff_X_add_C ht.le) _).mul
        (nonnegCoeff_rising (nonnegCoeff_X_add_C hu.le) _)) ?_
      (nonnegCoeff_ddiff ((nonnegCoeff_X_add_C ht.le).add (nonnegCoeff_natCast _))
        ((nonnegCoeff_X_add_C hu.le).add (nonnegCoeff_natCast _)) _)
    · exact (posUpTo_rising ht (r - 1)).mul
        (nonnegCoeff_rising (nonnegCoeff_X_add_C ht.le) _)
        (posUpTo_rising hu (r - 1))
        (nonnegCoeff_rising (nonnegCoeff_X_add_C hu.le) _)
    · have hm : (n - r) - (r - 1) = ((n - r) - (r - 1) - 1) + 1 := by omega
      rw [hm]
      exact posUpTo_ddiff ((nonnegCoeff_X_add_C ht.le).add (nonnegCoeff_natCast _))
        (posUpTo_X_add_C_natCast hu _)
        ((nonnegCoeff_X_add_C hu.le).add (nonnegCoeff_natCast _)) _
  · -- every other `s` contributes a nonnegative polynomial
    exact (nonnegCoeff_natCast _).mul (NonnegCoeff.sum _ _ (fun q _ =>
      (nonnegCoeff_natCast _).mul
        (((nonnegCoeff_rising (nonnegCoeff_X_add_C ht.le) _).mul
          (nonnegCoeff_rising (nonnegCoeff_X_add_C hu.le) _)).mul
          (nonnegCoeff_ddiff ((nonnegCoeff_X_add_C ht.le).add (nonnegCoeff_natCast _))
            ((nonnegCoeff_X_add_C hu.le).add (nonnegCoeff_natCast _)) _))))

end Nonneg

section FTC

/-! ### Extracting one `x`-coefficient

`Φ` lives in `ℝ[x][t]`, and the map taking the `x`-coefficient `j` is `ℝ`-linear but NOT
a ring hom, so `Polynomial.map` does not apply.  `coeffPoly` builds it by hand; the three
lemmas below are all that is needed to move between the two levels. -/

/-- The `x`-coefficient `j` of a polynomial in `t` over `ℝ[x]`, as a real polynomial in
`t`.  Coefficient extraction is `ℝ`-linear but not a ring hom, so `Polynomial.map` does
not apply and this has to be built by hand. -/
noncomputable def coeffPoly (j : ℕ) (Φ : (ℝ[X])[X]) : ℝ[X] :=
  ∑ i ∈ Finset.range (Φ.natDegree + 1), C ((Φ.coeff i).coeff j) * X ^ i

lemma coeffPoly_coeff (j : ℕ) (Φ : (ℝ[X])[X]) (i : ℕ) :
    (coeffPoly j Φ).coeff i = (Φ.coeff i).coeff j := by
  rw [coeffPoly, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq (Finset.range (Φ.natDegree + 1)) i
    (fun k => (Φ.coeff k).coeff j)]
  split_ifs with h
  · rfl
  · have hi : Φ.natDegree < i := by
      simp only [Finset.mem_range] at h
      omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hi]
    simp

lemma coeffPoly_derivative (j : ℕ) (Φ : (ℝ[X])[X]) :
    derivative (coeffPoly j Φ) = coeffPoly j (derivative Φ) := by
  ext i
  rw [Polynomial.coeff_derivative, coeffPoly_coeff, coeffPoly_coeff,
    Polynomial.coeff_derivative]
  have h : ((i : ℝ[X]) + 1) = C ((i : ℝ) + 1) := by
    rw [map_add, map_one, Polynomial.C_eq_natCast]
  rw [h, Polynomial.coeff_mul_C]

lemma coeffPoly_eval (j : ℕ) (Φ : (ℝ[X])[X]) (t : ℝ) :
    (coeffPoly j Φ).eval t = (Φ.eval (C t)).coeff j := by
  rw [coeffPoly, Polynomial.eval_finsetSum]
  rw [Polynomial.eval_eq_sum_range (p := Φ) (x := C t), Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
    ← Polynomial.C_pow, Polynomial.coeff_mul_C]

/-- A real polynomial with nonnegative derivative on `[a,b]` is monotone there. -/
lemma eval_mono_of_derivative_nonneg (P : ℝ[X]) {a b : ℝ} (hab : a ≤ b)
    (h : ∀ t ∈ Set.Icc a b, 0 ≤ (derivative P).eval t) :
    P.eval a ≤ P.eval b := by
  have hmono : MonotoneOn (fun t => P.eval t) (Set.Icc a b) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc a b) (P.continuous).continuousOn
      (fun x _ => (P.differentiable.differentiableAt).differentiableWithinAt) (fun x hx => ?_)
    rw [Polynomial.deriv]
    exact h x (interior_subset hx)
  exact hmono (Set.left_mem_Icc.2 hab) (Set.right_mem_Icc.2 hab) hab

end FTC

/-! ### The polynomials -/

/-- The bracket `(x+α)_k (x+β)_m - (x+α+β)_k (x)_m`, indexed by a pair `p = (k, m)`. -/
noncomputable def term (α β : ℝ) (p : ℕ × ℕ) : ℝ[X] :=
  rising (X + C α) p.1 * rising (X + C β) p.2
    - rising (X + C (α + β)) p.1 * rising (X : ℝ[X]) p.2

/-- The central truncation: the bracket summed over `r ≤ k` and `r ≤ m`. -/
noncomputable def V (n r : ℕ) (α β : ℝ) : ℝ[X] :=
  ∑ p ∈ (antidiagonal n).filter (fun p => r ≤ p.1 ∧ r ≤ p.2),
    (n.choose p.1 : ℝ[X]) * term α β p

/-- Karp's polynomial `Q_n^{α,β}`. -/
noncomputable def Q (f : ℕ → ℝ) (n : ℕ) (α β : ℝ) : ℝ[X] :=
  ∑ p ∈ antidiagonal n, (n.choose p.1 : ℝ[X]) * C (f p.1 * f p.2) * term α β p

/-- The symmetric weights `W j = f j * f (n-j)`. -/
noncomputable def W (f : ℕ → ℝ) (n j : ℕ) : ℝ := f j * f (n - j)

/-- **`Q` measures deviation from Vandermonde.**  At `r = 0` both halves of the bracket
collapse to the same value, because `(x+α) + (x+β) = (x+α+β) + x`. -/
theorem V_zero (n : ℕ) (α β : ℝ) : V n 0 α β = 0 := by
  have hfil : (antidiagonal n).filter (fun p => 0 ≤ p.1 ∧ 0 ≤ p.2) = antidiagonal n := by
    apply Finset.filter_true_of_mem
    intro p _
    exact ⟨Nat.zero_le _, Nat.zero_le _⟩
  rw [V, hfil]
  have hsplit : ∀ p ∈ antidiagonal n, (n.choose p.1 : ℝ[X]) * term α β p
      = (n.choose p.1 : ℝ[X]) * (rising (X + C α) p.1 * rising (X + C β) p.2)
        - (n.choose p.1 : ℝ[X])
            * (rising (X + C (α + β)) p.1 * rising (X : ℝ[X]) p.2) := by
    intro p _
    rw [term, mul_sub]
  rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib, rising_vandermonde,
    rising_vandermonde]
  have : (X + C α) + (X + C β) = (X + C (α + β)) + (X : ℝ[X]) := by
    rw [C_add]; ring
  rw [this, sub_self]


/-- `V` is the difference of the truncation at two points with the same argument sum. -/
theorem V_eq_trunc_sub (n r : ℕ) (α β : ℝ) :
    V n r α β = trunc n r (X + C α) (X + C β) - trunc n r (X + C (α + β)) X := by
  rw [V, trunc, trunc, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [term]
  ring

/-! ### The degree drops by two

Two separate cancellations.  Each `term` is a difference of two **monic** degree-`n`
products, which kills `xⁿ`.  The `x^{n-1}` coefficient of a single term does *not*
vanish — it is `(m-k)β` — and cancels only after summing, by pairing `(k,m)` with
`(m,k)` across the symmetric filter range, where `C(n,k) = C(n,m)`. -/

lemma nextCoeff_prod_X_add_C (g : ℕ → ℝ) (k : ℕ) :
    (∏ i ∈ range k, (X + C (g i))).nextCoeff = ∑ i ∈ range k, g i := by
  induction k with
  | zero => simp [nextCoeff]
  | succ m ih =>
    rw [Finset.prod_range_succ, Finset.sum_range_succ,
      Monic.nextCoeff_mul (monic_prod_of_monic _ _ (fun i _ => monic_X_add_C _))
        (monic_X_add_C _), ih, nextCoeff_X_add_C]

lemma rising_eq_prod (a : ℝ) (k : ℕ) :
    rising (X + C a) k = ∏ i ∈ range k, (X + C (a + (i : ℝ))) := by
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [C_add, Polynomial.C_eq_natCast]
  ring

lemma rising_monic (a : ℝ) (k : ℕ) : (rising (X + C a) k).Monic := by
  rw [rising_eq_prod]
  exact monic_prod_of_monic _ _ (fun i _ => monic_X_add_C _)

lemma rising_natDegree (a : ℝ) (k : ℕ) : (rising (X + C a) k).natDegree = k := by
  have hdeg : ∀ i ∈ range k, (X + C (a + (i : ℝ))).natDegree = 1 :=
    fun i _ => natDegree_X_add_C _
  rw [rising_eq_prod, natDegree_prod _ _ (fun i _ => (monic_X_add_C _).ne_zero),
    Finset.sum_congr rfl hdeg]
  simp

lemma rising_nextCoeff (a : ℝ) (k : ℕ) :
    (rising (X + C a) k).nextCoeff = ∑ i ∈ range k, (a + (i : ℝ)) := by
  rw [rising_eq_prod, nextCoeff_prod_X_add_C]

/-! `rising X m` is the `a = 0` case. -/

lemma rising_X_monic (m : ℕ) : (rising (X : ℝ[X]) m).Monic := by
  simpa using rising_monic (0 : ℝ) m

lemma rising_X_natDegree (m : ℕ) : (rising (X : ℝ[X]) m).natDegree = m := by
  simpa using rising_natDegree (0 : ℝ) m

lemma rising_X_nextCoeff (m : ℕ) :
    (rising (X : ℝ[X]) m).nextCoeff = ∑ i ∈ range m, (i : ℝ) := by
  simpa using rising_nextCoeff (0 : ℝ) m

/-! The two halves of a `term` are monic of the same degree `k + m`. -/

lemma termA_monic (α β : ℝ) (p : ℕ × ℕ) :
    (rising (X + C α) p.1 * rising (X + C β) p.2).Monic :=
  (rising_monic α p.1).mul (rising_monic β p.2)

lemma termA_natDegree (α β : ℝ) (p : ℕ × ℕ) :
    (rising (X + C α) p.1 * rising (X + C β) p.2).natDegree = p.1 + p.2 := by
  rw [(rising_monic α p.1).natDegree_mul (rising_monic β p.2), rising_natDegree,
    rising_natDegree]

lemma termB_monic (α β : ℝ) (p : ℕ × ℕ) :
    (rising (X + C (α + β)) p.1 * rising (X : ℝ[X]) p.2).Monic :=
  (rising_monic (α + β) p.1).mul (rising_X_monic p.2)

lemma termB_natDegree (α β : ℝ) (p : ℕ × ℕ) :
    (rising (X + C (α + β)) p.1 * rising (X : ℝ[X]) p.2).natDegree = p.1 + p.2 := by
  rw [(rising_monic (α + β) p.1).natDegree_mul (rising_X_monic p.2), rising_natDegree,
    rising_X_natDegree]

/-- The leading terms cancel: both halves are monic of degree `k + m`. -/
lemma term_coeff_top (α β : ℝ) (p : ℕ × ℕ) : (term α β p).coeff (p.1 + p.2) = 0 := by
  have hA := (termA_monic α β p).coeff_natDegree
  have hB := (termB_monic α β p).coeff_natDegree
  rw [termA_natDegree] at hA
  rw [termB_natDegree] at hB
  rw [term, coeff_sub, hA, hB, sub_self]

lemma term_coeff_gt (α β : ℝ) (p : ℕ × ℕ) {j : ℕ} (hj : p.1 + p.2 < j) :
    (term α β p).coeff j = 0 := by
  rw [term, coeff_sub,
    coeff_eq_zero_of_natDegree_lt (by rw [termA_natDegree]; exact hj),
    coeff_eq_zero_of_natDegree_lt (by rw [termB_natDegree]; exact hj), sub_zero]

/-- **The subleading coefficient is `(m - k)β`** — it does *not* vanish termwise. -/
lemma term_coeff_sub (α β : ℝ) (p : ℕ × ℕ) (h : 1 ≤ p.1 + p.2) :
    (term α β p).coeff (p.1 + p.2 - 1) = ((p.2 : ℝ) - (p.1 : ℝ)) * β := by
  have hA : (rising (X + C α) p.1 * rising (X + C β) p.2).coeff (p.1 + p.2 - 1)
      = (∑ i ∈ range p.1, (α + (i : ℝ))) + ∑ i ∈ range p.2, (β + (i : ℝ)) := by
    have hpos : 0 < (rising (X + C α) p.1 * rising (X + C β) p.2).natDegree := by
      rw [termA_natDegree]; omega
    rw [← termA_natDegree α β p, ← nextCoeff_of_natDegree_pos hpos,
      Monic.nextCoeff_mul (rising_monic α p.1) (rising_monic β p.2),
      rising_nextCoeff, rising_nextCoeff]
  have hB : (rising (X + C (α + β)) p.1 * rising (X : ℝ[X]) p.2).coeff (p.1 + p.2 - 1)
      = (∑ i ∈ range p.1, ((α + β) + (i : ℝ))) + ∑ i ∈ range p.2, (i : ℝ) := by
    have hpos : 0 < (rising (X + C (α + β)) p.1 * rising (X : ℝ[X]) p.2).natDegree := by
      rw [termB_natDegree]; omega
    rw [← termB_natDegree α β p, ← nextCoeff_of_natDegree_pos hpos,
      Monic.nextCoeff_mul (rising_monic (α + β) p.1) (rising_X_monic p.2),
      rising_nextCoeff, rising_X_nextCoeff]
  have hsplit : ∀ (c : ℝ) (k : ℕ),
      ∑ i ∈ range k, (c + (i : ℝ)) = (k : ℝ) * c + ∑ i ∈ range k, (i : ℝ) := by
    intro c k
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.card_range]
  rw [term, coeff_sub, hA, hB, hsplit, hsplit, hsplit]
  ring

/-- `term_coeff_sub` phrased against the total `n`, which is how the sum uses it. -/
lemma term_coeff_sub' (α β : ℝ) {p : ℕ × ℕ} {n : ℕ} (hp : p.1 + p.2 = n) (hn : 1 ≤ n) :
    (term α β p).coeff (n - 1) = ((p.2 : ℝ) - (p.1 : ℝ)) * β := by
  subst hp; exact term_coeff_sub α β p hn

lemma V_coeff (n r : ℕ) (α β : ℝ) (N : ℕ) :
    (V n r α β).coeff N
      = ∑ p ∈ (antidiagonal n).filter (fun p => r ≤ p.1 ∧ r ≤ p.2),
          (n.choose p.1 : ℝ) * (term α β p).coeff N := by
  rw [V, Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [← Polynomial.C_eq_natCast, Polynomial.coeff_C_mul]

/-- **The subleading coefficients cancel under `(k,m) ↦ (m,k)`.**  The swap preserves the
filter range and `C(n,k) = C(n,m)` on the antidiagonal, while `(m-k)β` changes sign. -/
theorem V_coeff_sub (n r : ℕ) (α β : ℝ) (hn : 1 ≤ n) : (V n r α β).coeff (n - 1) = 0 := by
  rw [V_coeff]
  refine Finset.sum_involution (fun p _ => Prod.swap p) ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_antidiagonal] at hp
    have hsum : p.1 + p.2 = n := hp.1
    have hc : n.choose p.2 = n.choose p.1 := Nat.choose_symm_of_eq_add (by omega)
    rw [term_coeff_sub' α β hsum hn,
      term_coeff_sub' α β (p := Prod.swap p) (by simp; omega) hn]
    simp only [Prod.fst_swap, Prod.snd_swap, hc]
    ring
  · intro p hp hne
    simp only [Finset.mem_filter, Finset.mem_antidiagonal] at hp
    intro hfix
    apply hne
    have h12 : p.1 = p.2 := by
      have := congrArg Prod.fst hfix
      simpa using this.symm
    rw [term_coeff_sub' α β hp.1 hn, h12]
    ring
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_antidiagonal,
      Prod.fst_swap, Prod.snd_swap] at hp ⊢
    exact ⟨by omega, hp.2.2, hp.2.1⟩
  · intro p _
    exact Prod.swap_swap p

/-- **The degree drops from `n` to `n-2`.** -/
theorem V_natDegree_le (n r : ℕ) (α β : ℝ) : (V n r α β).natDegree ≤ n - 2 := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rcases eq_or_ne N (n - 1) with hcase | hcase
  · rcases Nat.eq_zero_or_pos n with hz | hpos
    · subst hz
      rw [V_coeff]
      refine Finset.sum_eq_zero (fun p hp => ?_)
      simp only [Finset.mem_filter, Finset.mem_antidiagonal] at hp
      rw [term_coeff_gt α β p (by omega), mul_zero]
    · rw [hcase, V_coeff_sub n r α β hpos]
  · rw [V_coeff]
    refine Finset.sum_eq_zero (fun p hp => ?_)
    simp only [Finset.mem_filter, Finset.mem_antidiagonal] at hp
    rcases eq_or_ne N n with hn | hn
    · rw [hn, ← hp.1, term_coeff_top α β p, mul_zero]
    · rw [term_coeff_gt α β p (by omega), mul_zero]

/-! ### The sequence weights

Strict log-concavity is stated with shifted indices (`f k * f (k+2) < f (k+1)²` for
`k + 2 ≤ n`) so that no `ℕ`-subtraction enters the hypothesis. -/

/-- A nonnegative sequence, strictly log-concave across the interior of `0 … n`. -/
structure LogConcave (f : ℕ → ℝ) (n : ℕ) : Prop where
  nonneg : ∀ k, k ≤ n → 0 ≤ f k
  strict : ∀ k, k + 2 ≤ n → f k * f (k + 2) < f (k + 1) * f (k + 1)

/-- An interior zero would give `0 = f k ^ 2 > f (k-1) * f (k+1) ≥ 0`. -/
theorem interior_pos {f : ℕ → ℝ} {n : ℕ} (h : LogConcave f n) {k : ℕ}
    (h1 : 1 ≤ k) (h2 : k + 1 ≤ n) : 0 < f k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rcases lt_or_eq_of_le (h.nonneg (j + 1) (by omega)) with hpos | hzero
  · exact hpos
  · exfalso
    have := h.strict j (by omega)
    rw [← hzero] at this
    nlinarith [h.nonneg j (by omega), h.nonneg (j + 2) (by omega)]

/-- **The log-concavity chain.**  Moving the two indices apart strictly decreases the
product.  Induction on `b`, cancelling the interior factor `f b > 0`. -/
theorem spread {f : ℕ → ℝ} {n : ℕ} (h : LogConcave f n) :
    ∀ b c : ℕ, c + 1 ≤ b → b + 1 ≤ n → f c * f (b + 1) < f (c + 1) * f b := by
  intro b
  induction b with
  | zero => intro c hc; omega
  | succ m ih =>
    intro c hc hn
    rcases eq_or_lt_of_le hc with heq | hlt
    · -- base: `b = c + 1`, which is exactly the log-concavity hypothesis at `c`
      have hcm : c = m := by omega
      subst hcm
      exact h.strict c (by omega)
    · -- step: `c + 1 ≤ m`, so the inductive hypothesis applies at `m`
      have hcm : c + 1 ≤ m := by omega
      have hIH := ih c hcm (by omega)
      have hstr := h.strict m (by omega)
      have hmp : 0 < f m := interior_pos h (by omega) (by omega)
      have hm1 : 0 < f (m + 1) := interior_pos h (by omega) (by omega)
      have hc1 : 0 < f (c + 1) := interior_pos h (by omega) (by omega)
      rcases eq_or_lt_of_le (h.nonneg (m + 2) (by omega)) with hz | hp
      · -- `f (m+2) = 0`: the left side is zero and the right side is strictly positive
        rw [← hz]
        nlinarith
      · nlinarith [h.nonneg c (by omega)]

/-- Hence the weights `W j = f j * f (n-j)` strictly increase up to the centre. -/
theorem weight_lt {f : ℕ → ℝ} {n : ℕ} (h : LogConcave f n) {i : ℕ}
    (hi : 2 * (i + 1) ≤ n) : W f n i < W f n (i + 1) := by
  have hb : (n - i - 1) + 1 = n - i := by omega
  have hsp := spread h (n - i - 1) i (by omega) (by omega)
  rw [hb] at hsp
  rw [W, W]
  have : n - (i + 1) = n - i - 1 := by omega
  rw [this]
  exact hsp

/-! ### Summation by parts

The layer-cake rewrite `W m = W 0 + ∑_{i<m} (W (i+1) - W i)` turns the weighted sum into
a nonnegative combination of the central truncations. -/

/-- On the antidiagonal the weight depends only on the distance to the centre. -/
lemma weight_at (f : ℕ → ℝ) {n : ℕ} {p : ℕ × ℕ} (hp : p ∈ antidiagonal n) :
    f p.1 * f p.2 = W f n (min p.1 p.2) := by
  have hsum : p.1 + p.2 = n := by simpa using hp
  rcases le_total p.1 p.2 with h | h
  · rw [min_eq_left h, W, show n - p.1 = p.2 from by omega]
  · rw [min_eq_right h, W, show n - p.2 = p.1 from by omega, mul_comm]

lemma weight_telescope (f : ℕ → ℝ) (n m : ℕ) :
    W f n m = W f n 0 + ∑ i ∈ range m, (W f n (i + 1) - W f n i) := by
  rw [Finset.sum_range_sub (fun i => W f n i)]
  ring

/-- **The write-up's summation by parts.**  `Q` is a combination of the central
truncations with the weight increments as coefficients; the `r = 0` layer contributes
nothing because `V n 0 = 0`. -/
theorem decomposition (f : ℕ → ℝ) (n : ℕ) (α β : ℝ) :
    Q f n α β = ∑ i ∈ range (n / 2), C (W f n (i + 1) - W f n i) * V n (i + 1) α β := by
  have step : ∀ p ∈ antidiagonal n,
      (n.choose p.1 : ℝ[X]) * C (f p.1 * f p.2) * term α β p
        = (n.choose p.1 : ℝ[X]) * C (W f n 0) * term α β p
          + ∑ i ∈ range (min p.1 p.2),
              C (W f n (i + 1) - W f n i) * ((n.choose p.1 : ℝ[X]) * term α β p) := by
    intro p hp
    rw [weight_at f hp, weight_telescope, C_add, map_sum, mul_add, add_mul]
    congr 1
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [Q, Finset.sum_congr rfl step, Finset.sum_add_distrib]
  have hzero : ∑ p ∈ antidiagonal n, (n.choose p.1 : ℝ[X]) * C (W f n 0) * term α β p = 0 := by
    have : ∀ p ∈ antidiagonal n, (n.choose p.1 : ℝ[X]) * C (W f n 0) * term α β p
        = C (W f n 0) * ((n.choose p.1 : ℝ[X]) * term α β p) := fun p _ => by ring
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum]
    have hV : V n 0 α β = ∑ p ∈ antidiagonal n, (n.choose p.1 : ℝ[X]) * term α β p := by
      rw [V, Finset.filter_true_of_mem (fun p _ => ⟨Nat.zero_le _, Nat.zero_le _⟩)]
    rw [← hV, V_zero, mul_zero]
  rw [hzero, zero_add]
  rw [Finset.sum_comm' (t' := range (n / 2))
    (s' := fun i => (antidiagonal n).filter (fun p => i + 1 ≤ p.1 ∧ i + 1 ≤ p.2)) ?_]
  · exact Finset.sum_congr rfl (fun i _ => by rw [V, Finset.mul_sum])
  · intro p i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_antidiagonal, Nat.lt_min]
    omega

/-- **The degree of `Q` is at most `n-2`** — no longer carried: it follows from
`V_natDegree_le`, which is proved above. -/
theorem Q_natDegree_le (f : ℕ → ℝ) (n : ℕ) (α β : ℝ) :
    (Q f n α β).natDegree ≤ n - 2 := by
  rw [decomposition]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun i _ => ?_)
  exact le_trans (Polynomial.natDegree_C_mul_le _ _) (V_natDegree_le n (i + 1) α β)

section Assembly

/-- **Lemma 2's nonnegativity conclusion.**  With `0 ≤ α ≤ β`, every coefficient of `V`
is nonnegative.  Along the balancing line the derivative of the `j`-th coefficient is
`(c - 2t)` times a nonnegative quantity throughout `[0, α]`, so the coefficient is
monotone there, and its endpoints are exactly the two truncations `V` compares. -/
theorem V_coeff_nonneg (n r : ℕ) {α β : ℝ} (hα : 0 ≤ α) (hle : α ≤ β) (j : ℕ) :
    0 ≤ (V n r α β).coeff j := by
  have hderiv : ∀ t ∈ Set.Icc (0 : ℝ) α,
      0 ≤ (derivative (coeffPoly j (trunc n r aLine (bLine (α + β))))).eval t := by
    intro t ht
    simp only [Set.mem_Icc] at ht
    rw [coeffPoly_derivative, coeffPoly_eval,
      derivative_trunc_line n r aLine (bLine (α + β)) derivative_aLine
        (derivative_bLine (α + β)),
      Polynomial.eval_mul, Polynomial.eval_sub, eval_aLine, eval_bLine, eval_Rfun_line]
    have hC2 : Polynomial.C (α + β - t - t)
        = Polynomial.C (α + β - t) - Polynomial.C t := by
      rw [← Polynomial.C_sub]
    have hCC : (Polynomial.X + Polynomial.C (α + β - t))
          - (Polynomial.X + Polynomial.C t) = Polynomial.C (α + β - t - t) := by
      rw [hC2]; ring
    rw [hCC, Polynomial.coeff_C_mul]
    exact mul_nonneg (by linarith) (nonnegCoeff_Rfun_line n r ht.1 (by linarith) j)
  have hmono := eval_mono_of_derivative_nonneg
    (coeffPoly j (trunc n r aLine (bLine (α + β)))) hα hderiv
  rw [coeffPoly_eval, coeffPoly_eval, eval_trunc_line, eval_trunc_line] at hmono
  rw [show α + β - α = β from by ring, show α + β - 0 = α + β from by ring,
    show (Polynomial.X + Polynomial.C (0 : ℝ)) = Polynomial.X from by simp,
    trunc_symm n r Polynomial.X (Polynomial.X + Polynomial.C (α + β))] at hmono
  rw [V_eq_trunc_sub, Polynomial.coeff_sub]
  linarith

end Assembly


/-- Strict version of the monotonicity step. -/
lemma eval_strictMono_of_derivative_pos (P : ℝ[X]) {a b : ℝ} (hab : a < b)
    (h : ∀ t ∈ Set.Ioo a b, 0 < (derivative P).eval t) :
    P.eval a < P.eval b := by
  have hmono : StrictMonoOn (fun t => P.eval t) (Set.Icc a b) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc a b) (P.continuous).continuousOn
      (fun x hx => ?_)
    rw [Polynomial.deriv, interior_Icc] at *
    exact h x hx
  exact hmono (Set.left_mem_Icc.2 hab.le) (Set.right_mem_Icc.2 hab.le) hab

/-- `V` is symmetric in `α` and `β`. -/
theorem V_symm (n r : ℕ) (α β : ℝ) : V n r α β = V n r β α := by
  rw [V_eq_trunc_sub, V_eq_trunc_sub, trunc_symm n r (X + C α) (X + C β),
    show β + α = α + β from by ring]

/-- **Karp's strict positivity, for `α ≤ β`.** -/
theorem V_coeff_pos_of_le (n r : ℕ) (hr : 1 ≤ r) (hrn : 2 * r ≤ n)
    {α β : ℝ} (hα : 0 < α) (hle : α ≤ β) (j : ℕ) (hj : j + 2 ≤ n) :
    0 < (V n r α β).coeff j := by
  have hderiv : ∀ t ∈ Set.Ioo (0 : ℝ) α,
      0 < (derivative (coeffPoly j (trunc n r aLine (bLine (α + β))))).eval t := by
    intro t ht
    simp only [Set.mem_Ioo] at ht
    rw [coeffPoly_derivative, coeffPoly_eval,
      derivative_trunc_line n r aLine (bLine (α + β)) derivative_aLine
        (derivative_bLine (α + β)),
      Polynomial.eval_mul, Polynomial.eval_sub, eval_aLine, eval_bLine, eval_Rfun_line]
    have hC2 : Polynomial.C (α + β - t - t)
        = Polynomial.C (α + β - t) - Polynomial.C t := by rw [← Polynomial.C_sub]
    have hCC : (Polynomial.X + Polynomial.C (α + β - t))
          - (Polynomial.X + Polynomial.C t) = Polynomial.C (α + β - t - t) := by
      rw [hC2]; ring
    rw [hCC, Polynomial.coeff_C_mul]
    exact mul_pos (by linarith)
      (posUpTo_Rfun_line n r hr hrn ht.1 (by linarith) j (by omega))
  have hmono := eval_strictMono_of_derivative_pos
    (coeffPoly j (trunc n r aLine (bLine (α + β)))) hα hderiv
  rw [coeffPoly_eval, coeffPoly_eval, eval_trunc_line, eval_trunc_line] at hmono
  rw [show α + β - α = β from by ring, show α + β - 0 = α + β from by ring,
    show (Polynomial.X + Polynomial.C (0 : ℝ)) = Polynomial.X from by simp,
    trunc_symm n r Polynomial.X (Polynomial.X + Polynomial.C (α + β))] at hmono
  rw [V_eq_trunc_sub, Polynomial.coeff_sub]
  linarith

/-- **Karp's strict positivity, in the form the conjecture needs.** -/
theorem V_coeff_pos_thm (n r j : ℕ) (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hr : 1 ≤ r) (hrn : r ≤ n / 2) (hj : j + 2 ≤ n) : 0 < (V n r α β).coeff j := by
  rcases le_total α β with h | h
  · exact V_coeff_pos_of_le n r hr (by omega) hα h j hj
  · rw [V_symm]
    exact V_coeff_pos_of_le n r hr (by omega) hβ h j hj

/-! ### Karp's Conjecture 1 -/

/-- **Karp's Conjecture 1.**  For `n ≥ 3`, a nonnegative strictly log-concave weight
sequence and `α, β > 0`, every coefficient `x^j` of `Q` with `0 ≤ j ≤ n-2` is strictly
positive.  Nothing is carried: the decomposition supplies the positive weights and
`V_coeff_pos_thm` the strict positivity of each central truncation. -/
theorem karp (f : ℕ → ℝ) (n : ℕ) (hn : 3 ≤ n) (h : LogConcave f n)
    (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (j : ℕ) (hj : j + 2 ≤ n) :
    0 < (Q f n α β).coeff j := by
  rw [decomposition, Polynomial.finsetSum_coeff]
  refine Finset.sum_pos (fun i hi => ?_) ⟨0, by simp; omega⟩
  rw [Finset.mem_range] at hi
  rw [Polynomial.coeff_C_mul]
  refine mul_pos ?_ (V_coeff_pos_thm n (i + 1) j α β hα hβ (by omega) (by omega) hj)
  have := weight_lt h (i := i) (by omega)
  linarith

/-- And the degree is exactly `n-2`. -/
theorem degree_eq (f : ℕ → ℝ) (n : ℕ) (hn : 3 ≤ n) (h : LogConcave f n)
    (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    (Q f n α β).natDegree = n - 2 := by
  refine le_antisymm (Q_natDegree_le f n α β) (Polynomial.le_natDegree_of_ne_zero ?_)
  exact ne_of_gt (karp f n hn h α β hα hβ (n - 2) (by omega))

section Existence

/-! ### The class Karp's Conjecture quantifies over is inhabited

`karp` is this row's headline, and it is stated for every `f` with `LogConcave f n` — which is
the right formalisation, since the conjecture is about a CLASS of weight sequences. But nothing
produced a member of that class, and over an empty class the theorem says nothing.

`k ↦ (1/2)^(k²)` is strictly log-concave: the exponents satisfy `k² + (k+2)² = 2(k+1)² + 2`, so
the outer product is the inner one times `(1/2)²`, and the inner one is positive. No `Nat`
subtraction and no monotonicity lemma for a base below one is needed — the exponent identity
does it.
-/

/-- A strictly log-concave nonnegative sequence, for every length. -/
theorem logConcave_half_pow_sq (n : ℕ) : LogConcave (fun k => (1 / 2 : ℝ) ^ (k ^ 2)) n where
  nonneg := fun k _ => by positivity
  strict := fun k _ => by
    show (1 / 2 : ℝ) ^ (k ^ 2) * (1 / 2 : ℝ) ^ ((k + 2) ^ 2)
      < (1 / 2 : ℝ) ^ ((k + 1) ^ 2) * (1 / 2 : ℝ) ^ ((k + 1) ^ 2)
    rw [← pow_add, ← pow_add]
    have hexp : k ^ 2 + (k + 2) ^ 2 = ((k + 1) ^ 2 + (k + 1) ^ 2) + 2 := by ring
    rw [hexp, pow_add]
    have hpos : (0 : ℝ) < (1 / 2 : ℝ) ^ ((k + 1) ^ 2 + (k + 1) ^ 2) := by positivity
    have h4 : ((1 : ℝ) / 2) ^ (2 : ℕ) = 1 / 4 := by norm_num
    rw [h4]
    nlinarith [hpos]

/-- **`LogConcave` is inhabited**, so `karp` is not vacuous. -/
theorem exists_logConcave (n : ℕ) : ∃ f : ℕ → ℝ, LogConcave f n :=
  ⟨fun k => (1 / 2 : ℝ) ^ (k ^ 2), logConcave_half_pow_sq n⟩

end Existence

end Principia.MathDB.P323156
