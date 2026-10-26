import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Zify
import Mathlib.Order.Interval.Finset.Nat

set_option autoImplicit false

/-!
# MathDB #371228 — Chamberland–Dilcher's disjoint zero-block conjecture

Write-up: `mathdb-open-problems/problems/371228/solution.tex`, collaborator branch
`mathdb-results` of `antoshashakov/Principia-Math-In-Progress` (enrolled here 2026-09-29; it is
one of the NINE solutions added upstream since the work-list was last derived — the branch moved
from `b210789d` to `93ea328d` and the third hundred grew from 30 to 39).
Source: M. Chamberland and K. Dilcher, Equation (2.3) and **Conjecture 2.1**.

For odd `n`, with `N = (n-1)/2`, the source studies

`d_n(ℓ) = ⌊√(2ℓn)⌋ - ⌊√((2ℓ-1)n)⌋` for `1 ≤ ℓ ≤ N`,

and conjectures that each surplus value `d_n(λ) = δ ≥ 2` can be matched with `δ - 1` *consecutive*
zero positions, different `λ` giving *disjoint* blocks, all inside `{1, …, N}`.

## The mechanism, and one simplification over the write-up

Everything is the reflection `k ↦ n - k`. The write-up runs it through the ceiling function
`c(k) = ⌈k²/n⌉`, using the identity `c(n-k) = n - 2k + c(k)` and a gap bound
`0 ≤ c(r+1) - c(r) ≤ 2` to pin `c(r)` and `c(r+1)`.

**Neither the ceiling function nor the gap bound is needed.** Every statement about `c` is a pair
of inequalities between `k²` and multiples of `n`, and under the substitution the inequalities map
to each other *exactly*, in both directions:

* `k² ≤ 2λn` becomes `r² ≤ (2ℓ-1)n`, and
* `(2λ-1)n < (k-1)²` becomes `2ℓn < (r+1)²`,

with `r = n - k` and `ℓ = N + 1 + λ - k`. Both are polynomial identities, so `reflect_fwd` and
`reflect_bwd` are a single `nlinarith` each, and the second is the first read backwards — which is
why no gap bound is required to force equality. This is the "heavy machinery the step did not
need" pattern: the ceiling function is scaffolding for a human reader, and the inequalities it
abbreviates are what the argument actually uses.

The algebra is stated over `ℤ` deliberately, so that `n - k` and `N + 1 + λ - k` are genuine
subtractions; over `ℕ` every one of them would be truncated and `nlinarith` would be fighting
side conditions rather than doing algebra.

## What this module proves

* `le_bhi_iff` / `alo_lt_iff` — the bucket characterisation, straight from `Nat.le_sqrt` and
  `Nat.sqrt_lt`: `k ≤ ⌊√(2λn)⌋ ↔ k² ≤ 2λn` and `⌊√((2λ-1)n)⌋ < k ↔ (2λ-1)n < k²`.
* `dseq_eq_zero_iff` — `d_n(ℓ) = 0` is exactly `b_ℓ² ≤ (2ℓ-1)n`, because `a_ℓ ≤ b_ℓ` always.
* `reflect_fwd` / `reflect_bwd` — the reflection algebra, over `ℤ`.
* `forward` — **the block construction**: for `1 ≤ λ ≤ N` and `a_λ + 2 ≤ k ≤ b_λ`, the index `ℓ`
  with `k + ℓ = N + 1 + λ` satisfies `1 ≤ ℓ ≤ N` and `d_n(ℓ) = 0`. The interval membership is
  *proved*, not assumed — the write-up is explicit that choosing zeros beyond `N` would not answer
  the source's question.
* `forward_inj` — distinct pairs `(λ, k)` give distinct `ℓ`, which is the disjointness of the
  blocks.

## THE CONJECTURE IS PROVED -- `conjecture_2_1`

Stage 2 closed what the section above listed. `conjecture_2_1` states Chamberland-Dilcher's
Conjecture 2.1: for every `l`, being a zero of `d_n` in `{1,...,N}` is **equivalent** to lying in
the block `[L_lam, L_lam + d_n(lam) - 2]` of some surplus position `lam`. With `forward_inj`
(distinct pairs give distinct `l`) and `mem_block_iff` (each block is an interval of exactly
`d_n(lam) - 1` **consecutive** positions), that is the whole conjecture: consecutive blocks,
disjoint, inside the required finite interval, covering exactly the zeros.

* `bhi_lt` -- `b_l < l + N` for a zero `l` in range, with slack `(N + 1 - l)^2 >= 1`. This is
  where `l <= N` is exactly the hypothesis needed, and it is what makes `lam = l + N - b_l`
  positive.
* `backward` -- the surjectivity. `reflect_bwd` supplies the two inequalities; the rest is
  bounding `lam` between `1` and `N`, for which the only nonlinear fact needed is
  `(2N)^2 < (2N+1)^2`, handed to `omega` explicitly since `omega` is linear and both sides are
  opaque products.
* `mem_block_iff` -- the block shape, by `omega` once `dseq` is unfolded and `alo_le_bhi` and
  `bhi_le` are in scope.

Nothing in this file is now hypothetical.

-/

namespace Principia.MathDB.P371228

/-! ## The two floors and the sequence -/

/-- `⌊√((2ℓ-1)n)⌋`. -/
def alo (n l : ℕ) : ℕ := Nat.sqrt ((2 * l - 1) * n)

/-- `⌊√(2ℓn)⌋`. -/
def bhi (n l : ℕ) : ℕ := Nat.sqrt (2 * l * n)

/-- Chamberland–Dilcher's `d_n(ℓ)`. -/
def dseq (n l : ℕ) : ℕ := bhi n l - alo n l

theorem le_bhi_iff (n l k : ℕ) : k ≤ bhi n l ↔ k * k ≤ 2 * l * n := Nat.le_sqrt

theorem alo_lt_iff (n l k : ℕ) : alo n l < k ↔ (2 * l - 1) * n < k * k := Nat.sqrt_lt

theorem alo_le_bhi (n l : ℕ) : alo n l ≤ bhi n l :=
  Nat.sqrt_le_sqrt (Nat.mul_le_mul_right n (by omega))

/-- `d_n(ℓ) = 0` is exactly `b_ℓ² ≤ (2ℓ-1)n`. -/
theorem dseq_eq_zero_iff (n l : ℕ) :
    dseq n l = 0 ↔ bhi n l * bhi n l ≤ (2 * l - 1) * n := by
  rw [dseq, Nat.sub_eq_zero_iff_le]
  constructor
  · intro h
    exact le_trans (Nat.mul_le_mul h h) (Nat.sqrt_le _)
  · intro h
    exact Nat.le_sqrt.mpr h

/-! ## The reflection algebra, over `ℤ` -/

/-- Forward: the bucket inequalities at `(λ, k)` become the zero inequalities at `ℓ`. -/
theorem reflect_fwd (N lam k l r : ℤ) (hr : r = 2 * N + 1 - k) (hl : l = N + 1 + lam - k)
    (hA : k * k ≤ 2 * lam * (2 * N + 1))
    (hB : (2 * lam - 1) * (2 * N + 1) < (k - 1) * (k - 1)) :
    r * r ≤ (2 * l - 1) * (2 * N + 1) ∧ 2 * l * (2 * N + 1) < (r + 1) * (r + 1) := by
  subst hr
  subst hl
  constructor <;> nlinarith [hA, hB]

/-- Backward: the same identities read the other way. No gap bound is needed. -/
theorem reflect_bwd (N lam k l r : ℤ) (hk : k = 2 * N + 1 - r) (hlam : lam = l + N - r)
    (hA : r * r ≤ (2 * l - 1) * (2 * N + 1))
    (hB : 2 * l * (2 * N + 1) < (r + 1) * (r + 1)) :
    k * k ≤ 2 * lam * (2 * N + 1) ∧
      (2 * lam - 1) * (2 * N + 1) < (k - 1) * (k - 1) := by
  subst hk
  subst hlam
  constructor <;> nlinarith [hA, hB]

/-! ## The block construction -/

/-- A lower bound on `a_λ` that keeps the block inside `{1,…,N}`: since `n ≥ 2λ+1`, we have
`(2λ-1)n ≥ (2λ-1)(2λ+1) = 4λ²-1 ≥ (2λ-1)²`, so `a_λ ≥ 2λ-1`. -/
theorem le_alo (N lam : ℕ) (h1 : 1 ≤ lam) (h2 : lam ≤ N) :
    2 * lam - 1 ≤ alo (2 * N + 1) lam := by
  rw [alo]
  refine Nat.le_sqrt.mpr ?_
  have h : (2 * lam - 1) * (2 * lam - 1) ≤ (2 * lam - 1) * (2 * N + 1) :=
    Nat.mul_le_mul_left _ (by omega)
  exact h

/-- An upper bound on `b_λ`: `2λn < (N+λ+1)²`, since the difference is `(N-λ)² + 2N + 1 > 0`. -/
theorem bhi_le (N lam : ℕ) (h1 : 1 ≤ lam) (h2 : lam ≤ N) :
    bhi (2 * N + 1) lam ≤ N + lam := by
  rw [bhi]
  have h : 2 * lam * (2 * N + 1) < (N + lam + 1) * (N + lam + 1) := by nlinarith
  exact Nat.lt_succ_iff.mp (Nat.sqrt_lt.mpr h)

/-- **The block construction.** For `1 ≤ λ ≤ N` and `a_λ + 2 ≤ k ≤ b_λ`, the index `ℓ` paired with
`k` by `k + ℓ = N + 1 + λ` lies in `{1,…,N}` and is a zero of `d_n`. -/
theorem forward (N lam k l : ℕ) (h1 : 1 ≤ lam) (h2 : lam ≤ N)
    (hk1 : alo (2 * N + 1) lam + 2 ≤ k) (hk2 : k ≤ bhi (2 * N + 1) lam)
    (hl : k + l = N + 1 + lam) :
    1 ≤ l ∧ l ≤ N ∧ dseq (2 * N + 1) l = 0 ∧ bhi (2 * N + 1) l + k = 2 * N + 1 := by
  have hlo := le_alo N lam h1 h2
  have hhi := bhi_le N lam h1 h2
  -- the interval, proved rather than assumed
  have hlge : 1 ≤ l := by omega
  have hlle : l ≤ N := by omega
  -- the bucket inequalities at `(λ, k)`, in `ℕ`
  have hA : k * k ≤ 2 * lam * (2 * N + 1) := (le_bhi_iff _ _ _).mp hk2
  have hB : (2 * lam - 1) * (2 * N + 1) < (k - 1) * (k - 1) :=
    (alo_lt_iff _ _ _).mp (by omega)
  -- transport to `ℤ`, where the reflection is an honest subtraction
  set r : ℕ := 2 * N + 1 - k with hrdef
  have hkn : k ≤ 2 * N + 1 := by omega
  have hAz : (k : ℤ) * k ≤ 2 * lam * (2 * N + 1) := by exact_mod_cast hA
  have hBz : (2 * (lam : ℤ) - 1) * (2 * N + 1) < ((k : ℤ) - 1) * ((k : ℤ) - 1) := by
    have hk2' : 1 ≤ k := by omega
    zify [hk2', show 1 ≤ 2 * lam from by omega] at hB
    exact hB
  obtain ⟨hz1, hz2⟩ :=
    reflect_fwd N lam k l r (by rw [hrdef]; push_cast [hkn]; ring)
      (by omega) hAz hBz
  -- back to `ℕ`, where the two floors now agree
  have hz1' : r * r ≤ (2 * l - 1) * (2 * N + 1) := by
    have h1l : 1 ≤ l := hlge
    zify [show 1 ≤ 2 * l from by omega]
    exact hz1
  have hz2' : 2 * l * (2 * N + 1) < (r + 1) * (r + 1) := by exact_mod_cast hz2
  have hb : bhi (2 * N + 1) l = r := by
    refine le_antisymm ?_ ?_
    · exact Nat.lt_succ_iff.mp (Nat.sqrt_lt.mpr hz2')
    · exact Nat.le_sqrt.mpr (le_trans hz1' (Nat.mul_le_mul_right _ (by omega)))
  refine ⟨hlge, hlle, ?_, ?_⟩
  · rw [dseq_eq_zero_iff, hb]
    exact hz1'
  · omega

/-- **Disjointness**: two pairs `(λ, k)` and `(λ′, k′)` producing the same `ℓ` are equal. The
zero `ℓ` determines `b_ℓ`, hence `k = n - b_ℓ`, hence `λ`. -/
theorem forward_inj (N lam lam' k k' l : ℕ) (h1 : 1 ≤ lam) (h2 : lam ≤ N)
    (hk1 : alo (2 * N + 1) lam + 2 ≤ k) (hk2 : k ≤ bhi (2 * N + 1) lam)
    (hl : k + l = N + 1 + lam)
    (h1' : 1 ≤ lam') (h2' : lam' ≤ N)
    (hk1' : alo (2 * N + 1) lam' + 2 ≤ k') (hk2' : k' ≤ bhi (2 * N + 1) lam')
    (hl' : k' + l = N + 1 + lam') :
    lam = lam' ∧ k = k' := by
  obtain ⟨-, -, -, hb⟩ := forward N lam k l h1 h2 hk1 hk2 hl
  obtain ⟨-, -, -, hb'⟩ := forward N lam' k' l h1' h2' hk1' hk2' hl'
  omega

/-! ## Stage 2: the backward map, the block shape, and the conjecture

The two inequalities are `reflect_bwd`, already proved in stage 1; everything below is
`ℕ` plumbing plus one nonlinear step handed to `omega` explicitly. -/

/-- `b_ℓ < ℓ + N` whenever `1 ≤ ℓ ≤ N` and `d_n(ℓ) = 0`. The slack is `(N + 1 - ℓ)² ≥ 1`, which
is why `ℓ ≤ N` is exactly the hypothesis needed. -/
theorem bhi_lt (N l : ℕ) (h1 : 1 ≤ l) (h2 : l ≤ N) (hz : dseq (2 * N + 1) l = 0) :
    bhi (2 * N + 1) l < l + N := by
  have hr : bhi (2 * N + 1) l * bhi (2 * N + 1) l ≤ (2 * l - 1) * (2 * N + 1) :=
    (dseq_eq_zero_iff _ _).mp hz
  by_contra hc
  rw [Nat.not_lt] at hc
  have e : (2 * l - 1) * (2 * N + 1) + (N + 1 - l) * (N + 1 - l) = (l + N) * (l + N) := by
    zify [show l ≤ N + 1 from by omega, show 1 ≤ 2 * l from by omega]
    ring
  have hpos : 0 < (N + 1 - l) * (N + 1 - l) :=
    Nat.mul_pos (by omega) (by omega)
  have hsq : (l + N) * (l + N) ≤ bhi (2 * N + 1) l * bhi (2 * N + 1) l := Nat.mul_le_mul hc hc
  omega

/-- **The backward map.** Every zero in `{1,…,N}` arises from a pair `(λ, k)` in the block range.
The two inequalities are `reflect_bwd`, already proved; everything here is `ℕ` plumbing. -/
theorem backward (N l : ℕ) (h1 : 1 ≤ l) (h2 : l ≤ N) (hz : dseq (2 * N + 1) l = 0) :
    ∃ lam k, 1 ≤ lam ∧ lam ≤ N ∧ alo (2 * N + 1) lam + 2 ≤ k ∧
      k ≤ bhi (2 * N + 1) lam ∧ k + l = N + 1 + lam := by
  set r : ℕ := bhi (2 * N + 1) l with hrdef
  have hrlt : r < l + N := bhi_lt N l h1 h2 hz
  have hA : r * r ≤ (2 * l - 1) * (2 * N + 1) := (dseq_eq_zero_iff _ _).mp hz
  have hB : 2 * l * (2 * N + 1) < (r + 1) * (r + 1) := by
    rw [hrdef, bhi]
    exact Nat.lt_succ_sqrt _
  have hAz : (r : ℤ) * r ≤ (2 * (l : ℤ) - 1) * (2 * (N : ℤ) + 1) := by
    zify [show 1 ≤ 2 * l from by omega] at hA
    exact hA
  have hBz : 2 * (l : ℤ) * (2 * (N : ℤ) + 1) < ((r : ℤ) + 1) * ((r : ℤ) + 1) := by
    exact_mod_cast hB
  set k : ℕ := 2 * N + 1 - r with hkdef
  set lam : ℕ := l + N - r with hlamdef
  have hkz : (k : ℤ) = 2 * (N : ℤ) + 1 - (r : ℤ) := by rw [hkdef]; omega
  have hlamz : (lam : ℤ) = (l : ℤ) + (N : ℤ) - (r : ℤ) := by rw [hlamdef]; omega
  obtain ⟨hC, hD⟩ := reflect_bwd N lam k l r hkz hlamz hAz hBz
  have hlam1 : 1 ≤ lam := by omega
  have hk2 : 2 ≤ k := by omega
  have hC' : k * k ≤ 2 * lam * (2 * N + 1) := by exact_mod_cast hC
  have hD' : (2 * lam - 1) * (2 * N + 1) < (k - 1) * (k - 1) := by
    zify [show 1 ≤ k from by omega, show 1 ≤ 2 * lam from by omega]
    exact hD
  have hlamN : lam ≤ N := by
    by_contra hc
    have hbig : (2 * N + 1) * (2 * N + 1) ≤ (2 * lam - 1) * (2 * N + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    have hsmall : (k - 1) * (k - 1) ≤ (2 * N) * (2 * N) :=
      Nat.mul_le_mul (by omega) (by omega)
    -- omega is linear, so the one nonlinear step has to be handed to it
    have hne : (2 * N) * (2 * N) < (2 * N + 1) * (2 * N + 1) := by nlinarith
    omega
  refine ⟨lam, k, hlam1, hlamN, ?_, (le_bhi_iff _ _ _).mpr hC', by omega⟩
  have := (alo_lt_iff (2 * N + 1) lam (k - 1)).mpr hD'
  omega

/-! ### The block, as an interval -/

/-- The first element of the block attached to `λ`. -/
def blockL (N lam : ℕ) : ℕ := N + 1 + lam - bhi (2 * N + 1) lam

/-- The indices `ℓ` paired with `λ` are exactly the interval `[L_λ, L_λ + δ - 2]` — that is,
`δ - 1` **consecutive** positions, which is the conjecture's shape. -/
theorem mem_block_iff (N lam l : ℕ) (h1 : 1 ≤ lam) (h2 : lam ≤ N) :
    (∃ k, alo (2 * N + 1) lam + 2 ≤ k ∧ k ≤ bhi (2 * N + 1) lam ∧ k + l = N + 1 + lam)
      ↔ (blockL N lam ≤ l ∧ l ≤ blockL N lam + dseq (2 * N + 1) lam - 2 ∧
          2 ≤ dseq (2 * N + 1) lam) := by
  have hle := alo_le_bhi (2 * N + 1) lam
  have hbhi := bhi_le N lam h1 h2
  simp only [blockL, dseq]
  constructor
  · rintro ⟨k, hk1, hk2, hk3⟩
    omega
  · rintro ⟨hl1, hl2, hl3⟩
    exact ⟨N + 1 + lam - l, by omega, by omega, by omega⟩

/-- **Chamberland–Dilcher Conjecture 2.1.** The zeros of `d_n` in `{1,…,N}` are exactly the union
of the blocks `[L_λ, L_λ + d_n(λ) - 2]` over the surplus positions `λ`; each block is an interval
of `d_n(λ) - 1` consecutive positions, and by `forward_inj` distinct `λ` give disjoint blocks. -/
theorem conjecture_2_1 (N l : ℕ) :
    (1 ≤ l ∧ l ≤ N ∧ dseq (2 * N + 1) l = 0)
      ↔ ∃ lam, 1 ≤ lam ∧ lam ≤ N ∧ 2 ≤ dseq (2 * N + 1) lam ∧
          blockL N lam ≤ l ∧ l ≤ blockL N lam + dseq (2 * N + 1) lam - 2 := by
  constructor
  · rintro ⟨hl1, hl2, hz⟩
    obtain ⟨lam, k, hlam1, hlamN, hk1, hk2, hk3⟩ := backward N l hl1 hl2 hz
    obtain ⟨hb1, hb2, hb3⟩ :=
      (mem_block_iff N lam l hlam1 hlamN).mp ⟨k, hk1, hk2, hk3⟩
    exact ⟨lam, hlam1, hlamN, hb3, hb1, hb2⟩
  · rintro ⟨lam, hlam1, hlamN, hd, hb1, hb2⟩
    obtain ⟨k, hk1, hk2, hk3⟩ :=
      (mem_block_iff N lam l hlam1 hlamN).mpr ⟨hb1, hb2, hd⟩
    obtain ⟨h1, h2, h3, -⟩ := forward N lam k l hlam1 hlamN hk1 hk2 hk3
    exact ⟨h1, h2, h3⟩
end Principia.MathDB.P371228
