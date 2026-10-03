/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Erdos1054.Proofs.ReprElementary
import Principia.Common.PrimeSumExact.SubsetSums

set_option autoImplicit false

/-!
# `Comp_Verifier_window1` removed: the first window of `prop:fraiture-finite`, unconditionally

The spine's `Link_Step_FraitureFirstWindowCover` (EP1054.tex lines 757–767) takes the verifier
check `Comp_Verifier_window1`: (a) there are `94` primes in `(10 000, 10 883]`, (b) their subset
sums cover `[469 615, 480 503]`, (c) the hypothesis `p ≤ U − C + 1` of `lem:fraiture-extension`
holds for every prime `10 883 < p ≤ 98 999 987`, and (d) the final upper end is
`273 803 744 799 153`. Only (b) and (c) carry the induction; (d) only names its endpoint.

* (b) is `Principia.Common.PrimeSumExact.subsetSums_primes_Ioc_10000_10883` (a `decide +kernel`
  subset-sum bitset over the `94` primes).
* (c) needs no computation. The inclusive width of the certified interval after the primes of
  `(10 883, n]` is `10 889 + ∑_{10 883 < p ≤ n} p`, and `first_width` shows it is `≥ n + 1`:
  up to `21 777` the prime `10 889` alone suffices, above it Bertrand's postulate gives a prime of
  `(n/2, n]`, and strong induction at `n/2` does the rest. This is the argument of
  `Proofs.ReprElementary.large_width` for the large window, with `(4·10^7, 51 000 001)` replaced
  by `(10 883, 10 889)`.
* `cover_upto` is the extension induction for EVERY `n ≥ 10 883` (no upper limit and no exact
  sum): every `N ∈ [469 615, 480 503 + ∑_{10 883 < p ≤ n} p]` is a sum of distinct primes of
  `(10 000, n]`. The proof is `Proofs.link_Step_FraitureFirstWindowCover` with (b) as base case and
  `first_width` in place of (c).
* (d) is `Principia.Common.PrimeSumExact.sum_primes_window1` (the exact sum of the `5 705 800`
  primes, a chain of `decide +kernel` sieve segments). With it, `cover_upto` at `98 999 987` is the
  spine's `Step_FraitureFirstWindowCover` (`step_FraitureFirstWindowCover_unconditional`), and the
  whole check is a theorem (`input_Comp_Verifier_window1`).

**A route that avoids the exact sum.** `Eq_FraitureFirstWindow` also follows from
`Eq_FraitureLargeWindow` (`eq_FraitureFirstWindow_of_large`): the large window covers
`[105 000 001, 10^27 + 10^8]`, and below it `cover_upto` needs only the crude bound
`∑_{10 883 < p ≤ 98 999 987} p ≥ 10 000 019 + 98 999 987` (two explicit primes), after which
`lem:fraiture-prime-window` (`M = 10^4`, `Y = 99·10^6 < M²`) turns a nonempty subset sum `N − 1`
into `N ∈ 𝓡`.

No statement is weakened: every theorem's type is a spine `Prop`, the spine's link, or the
spine's `Step_FraitureFirstWindowCover` with (d) as its only hypothesis.
-/

namespace Principia.Erdos1054.Alt7.Window1

open Principia.Erdos1054

/-- `10 889`, the first prime after `10 883` (`10 884, …, 10 888` are composite). -/
theorem prime_10889 : Nat.Prime 10889 := by norm_num

/-- The first prime after `10^7`. -/
theorem prime_10000019 : Nat.Prime 10000019 := by norm_num

/-- The last prime of the first window, `98 999 987 ≤ Y = 99 000 000`. -/
theorem prime_98999987 : Nat.Prime 98999987 := by norm_num

/-- **The certified width stays ahead of the next prime** (check (c) of `Comp_Verifier_window1`,
without computation): for `n ≥ 10 883`, `n + 1 ≤ 10 889 + ∑_{10 883 < p ≤ n} p`. -/
theorem first_width (n : ℕ) (hn : 10883 ≤ n) :
    n + 1 ≤ 10889 + ∑ r ∈ (Finset.Ioc 10883 n).filter Nat.Prime, r := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h1 : n ≤ 10888
    · omega
    by_cases h2 : n < 21778
    · have hmem : 10889 ∈ (Finset.Ioc 10883 n).filter Nat.Prime := by
        rw [Finset.mem_filter, Finset.mem_Ioc]
        exact ⟨⟨by norm_num, by omega⟩, prime_10889⟩
      have hle : 10889 ≤ ∑ r ∈ (Finset.Ioc 10883 n).filter Nat.Prime, r :=
        Finset.single_le_sum (f := fun r : ℕ => r) (fun i _ => Nat.zero_le i) hmem
      omega
    · obtain ⟨m, hm⟩ : ∃ m, m = n / 2 := ⟨_, rfl⟩
      have hm1 : 10883 ≤ m := by omega
      have hm2 : m < n := by omega
      have ihm := ih m hm2 hm1
      obtain ⟨q, hq, hmq, hq2m⟩ := Nat.exists_prime_lt_and_le_two_mul m (by omega)
      have hsub : insert q ((Finset.Ioc 10883 m).filter Nat.Prime) ⊆
          (Finset.Ioc 10883 n).filter Nat.Prime := by
        intro x hx
        rw [Finset.mem_insert] at hx
        rw [Finset.mem_filter, Finset.mem_Ioc]
        rcases hx with rfl | hx
        · exact ⟨⟨by omega, by omega⟩, hq⟩
        · rw [Finset.mem_filter, Finset.mem_Ioc] at hx
          exact ⟨⟨hx.1.1, by omega⟩, hx.2⟩
      have hnotin : q ∉ (Finset.Ioc 10883 m).filter Nat.Prime := by
        intro hx
        rw [Finset.mem_filter, Finset.mem_Ioc] at hx
        omega
      have hle : ∑ r ∈ insert q ((Finset.Ioc 10883 m).filter Nat.Prime), r ≤
          ∑ r ∈ (Finset.Ioc 10883 n).filter Nat.Prime, r :=
        Finset.sum_le_sum_of_subset hsub
      rw [Finset.sum_insert hnotin] at hle
      omega

/-- **Check (c) of `Comp_Verifier_window1`, for every prime after `10 883`**: with `C = 469 615`
and the upper end `U = 480 503 + ∑_{10 883 < r < p} r`, the new prime satisfies
`p + C ≤ U + 1`. `first_width` at `p − 1`. -/
theorem window1_extension (p : ℕ) (h1 : 10883 < p) :
    p + 469615 ≤ 480503 + (∑ r ∈ (Finset.Ioo 10883 p).filter Nat.Prime, r) + 1 := by
  have hw := first_width (p - 1) (by omega)
  have e : Finset.Ioo 10883 p = Finset.Ioc 10883 (p - 1) := by
    ext x
    simp only [Finset.mem_Ioo, Finset.mem_Ioc]
    omega
  rw [e]
  omega

/-- **The first-window extension induction, for every `n ≥ 10 883`** (EP1054.tex lines 757–767):
every `N ∈ [469 615, 480 503 + ∑_{10 883 < p ≤ n} p]` is a sum of distinct primes of
`(10 000, n]`. The base case is the `94`-prime cover of `[469 615, 480 503]`
(`Principia.Common.PrimeSumExact.subsetSums_primes_Ioc_10000_10883`); each prime `n + 1` is
adjoined by `lem:fraiture-extension` (`Proofs.leaf_Lem_FraitureExtension`), its hypothesis being
`first_width n`. -/
theorem cover_upto (n : ℕ) (hn : 10883 ≤ n) : ∀ N : ℕ, 469615 ≤ N →
    N ≤ 480503 + ∑ r ∈ (Finset.Ioc 10883 n).filter Nat.Prime, r →
    N ∈ subsetSums ((Finset.Ioc 10000 n).filter Nat.Prime) := by
  have hExt : Lem_FraitureExtension := Proofs.leaf_Lem_FraitureExtension
  induction n, hn using Nat.le_induction with
  | base =>
    intro N hN1 hN2
    rw [Finset.Ioc_self, Finset.filter_empty, Finset.sum_empty] at hN2
    exact Principia.Common.PrimeSumExact.subsetSums_primes_Ioc_10000_10883 N hN1 (by omega)
  | succ n hn ih =>
    intro N hN1 hN2
    rw [← Finset.insert_Ioc_right_eq_Ioc_add_one hn, Finset.filter_insert] at hN2
    rw [← Finset.insert_Ioc_right_eq_Ioc_add_one (by omega : 10000 ≤ n), Finset.filter_insert]
    by_cases hp : (n + 1).Prime
    · rw [if_pos hp] at hN2 ⊢
      have hnotin : n + 1 ∉ (Finset.Ioc 10883 n).filter Nat.Prime := by simp
      rw [Finset.sum_insert hnotin] at hN2
      have hw := first_width n hn
      exact hExt 469615 (480503 + ∑ r ∈ (Finset.Ioc 10883 n).filter Nat.Prime, r) _ (n + 1)
        (by omega) (fun q hq => (Finset.mem_filter.1 hq).2) ih hp (by simp) (by omega)
        N hN1 (by omega)
    · rw [if_neg hp] at hN2 ⊢
      exact ih N hN1 hN2

/-- **`Step_FraitureFirstWindowCover` from the exact prime sum** (check (d) of
`Comp_Verifier_window1`, the only part of the check the step still needs):
`cover_upto` at `n = 98 999 987`.

**Remaining hypothesis:** `∑_{10 883 < p ≤ 98 999 987} p = 273 803 744 318 650`. -/
theorem step_FraitureFirstWindowCover_of_sum
    (hsum : ∑ r ∈ (Finset.Ioc 10883 98999987).filter Nat.Prime, r = 273803744318650) :
    Principia.Erdos1054.Step_FraitureFirstWindowCover := by
  intro N hN1 hN2
  exact cover_upto 98999987 (by norm_num) N hN1 (by omega)

/-- **`Step_FraitureFirstWindowCover`, unconditionally** (EP1054.tex lines 757–767): every
`N ∈ [469 615, 273 803 744 799 153]` is a sum of distinct primes of `(10 000, 98 999 987]`.
`step_FraitureFirstWindowCover_of_sum` at `Principia.Common.PrimeSumExact.sum_primes_window1`.

**Remaining hypotheses: none.** (Rounds 1–6: `Comp_Verifier_window1`.) -/
theorem step_FraitureFirstWindowCover_unconditional :
    Principia.Erdos1054.Step_FraitureFirstWindowCover :=
  step_FraitureFirstWindowCover_of_sum (by
    have h := Principia.Common.PrimeSumExact.sum_primes_window1
    omega)

/-- **`Comp_Verifier_window1`, proved** (check 2 of the verifier), exactly as stated:
(a) `Principia.Common.PrimeSumExact.card_primes_Ioc_10000_10883`,
(b) `Principia.Common.PrimeSumExact.subsetSums_primes_Ioc_10000_10883`,
(c) `window1_extension` (Bertrand, no computation),
(d) `Principia.Common.PrimeSumExact.sum_primes_window1`.

**Remaining hypotheses: none.** -/
theorem input_Comp_Verifier_window1 : Principia.Erdos1054.Comp_Verifier_window1 := by
  refine ⟨Principia.Common.PrimeSumExact.card_primes_Ioc_10000_10883,
    Principia.Common.PrimeSumExact.subsetSums_primes_Ioc_10000_10883,
    fun p _ h1 _ => window1_extension p h1, ?_⟩
  have h := Principia.Common.PrimeSumExact.sum_primes_window1
  omega

/-- Cross-check: the spine's own link `Proofs.link_Step_FraitureFirstWindowCover`, applied to
`Proofs.leaf_Lem_FraitureExtension` and `input_Comp_Verifier_window1`, gives the same step. -/
theorem step_FraitureFirstWindowCover_via_link :
    Principia.Erdos1054.Step_FraitureFirstWindowCover :=
  Proofs.link_Step_FraitureFirstWindowCover Proofs.leaf_Lem_FraitureExtension
    input_Comp_Verifier_window1

/-- **`Link_Step_FraitureFirstWindowCover` without its inputs**: the link's conclusion holds
outright, so neither `Lem_FraitureExtension` (as a binder) nor `Comp_Verifier_window1` is used. -/
theorem link_Step_FraitureFirstWindowCover_unconditional :
    Principia.Erdos1054.Spine.Link_Step_FraitureFirstWindowCover :=
  fun _ _ => step_FraitureFirstWindowCover_unconditional

/-- **`eq:fraiture-first-window`, unconditionally** (EP1054.tex lines 732–733): every
`N ∈ [469 616, 273 803 744 799 154]` is represented. The spine's
`Proofs.link_Eq_FraitureFirstWindow` at `step_FraitureFirstWindowCover_unconditional` and
`Proofs.leaf_Lem_FraiturePrimeWindow`.

**Remaining hypotheses: none.** (Rounds 1–6: `Comp_Verifier_window1`.) -/
theorem eq_FraitureFirstWindow_unconditional : Principia.Erdos1054.Eq_FraitureFirstWindow :=
  Proofs.link_Eq_FraitureFirstWindow step_FraitureFirstWindowCover_unconditional
    Proofs.leaf_Lem_FraiturePrimeWindow

/-! ## The route that needs no exact prime sum -/

/-- `a + b ≤ ∑ s` for two distinct members of a finset of naturals (stated for a variable finset,
so no concrete interval is ever unfolded). -/
theorem add_le_sum_of_mem (s : Finset ℕ) (a b : ℕ) (hab : a ≠ b) (ha : a ∈ s) (hb : b ∈ s) :
    a + b ≤ ∑ x ∈ s, x := by
  have hsub : ({a, b} : Finset ℕ) ⊆ s := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb
  have h := Finset.sum_le_sum_of_subset (f := fun x : ℕ => x) hsub
  rw [Finset.sum_pair hab] at h
  exact h

/-- **A crude lower bound on the first-window prime sum**, from two explicit primes:
`∑_{10 883 < p ≤ 98 999 987} p ≥ 10 000 019 + 98 999 987 = 109 000 006`. -/
theorem sum_primes_window1_ge :
    109000006 ≤ ∑ r ∈ (Finset.Ioc 10883 98999987).filter Nat.Prime, r := by
  have h1 : 10000019 ∈ (Finset.Ioc 10883 98999987).filter Nat.Prime := by
    rw [Finset.mem_filter, Finset.mem_Ioc]
    exact ⟨⟨by norm_num, by norm_num⟩, prime_10000019⟩
  have h2 : 98999987 ∈ (Finset.Ioc 10883 98999987).filter Nat.Prime := by
    rw [Finset.mem_filter, Finset.mem_Ioc]
    exact ⟨⟨by norm_num, le_rfl⟩, prime_98999987⟩
  have h := add_le_sum_of_mem _ 10000019 98999987 (by norm_num) h1 h2
  omega

/-- **The first window below `1.05·10^8`, with no exact sum**: every `N ∈ [469 615, 105 000 000]`
is a sum of distinct primes of `(10 000, 98 999 987]`. `cover_upto` at `98 999 987` with
`sum_primes_window1_ge`. -/
theorem cover_below_large (N : ℕ) (hN1 : 469615 ≤ N) (hN2 : N ≤ 105000000) :
    N ∈ subsetSums ((Finset.Ioc 10000 98999987).filter Nat.Prime) := by
  have hge := sum_primes_window1_ge
  exact cover_upto 98999987 (by norm_num) N hN1 (by omega)

/-- `lem:fraiture-prime-window` at `M = 10^4`, `Y = 99·10^6 < M²`: if `N − 1 ≥ 1` is a sum of
distinct primes of `(10 000, 98 999 987]` then `N ∈ 𝓡`. The body of
`Proofs.link_Eq_FraitureFirstWindow`, for one `N`. -/
theorem mem_R_of_cover (N : ℕ) (hN : 2 ≤ N)
    (hcov : N - 1 ∈ subsetSums ((Finset.Ioc 10000 98999987).filter Nat.Prime)) : N ∈ R := by
  obtain ⟨S, hS, hsum⟩ := hcov
  have hSne : S.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    rw [Finset.sum_empty] at hsum
    omega
  have hmem := Proofs.leaf_Lem_FraiturePrimeWindow 10000 99000000
    ((Finset.Ioc 10000 98999987).filter Nat.Prime) (by norm_num) (by norm_num) (by
      intro p hp
      rw [Finset.mem_filter, Finset.mem_Ioc] at hp
      have hp' : p ≤ 99000000 := by omega
      exact ⟨hp.2, by exact_mod_cast hp.1.1, by exact_mod_cast hp'⟩) S hS hSne
  rw [hsum] at hmem
  have e : N = 1 + (N - 1) := by omega
  rw [e]
  exact hmem

/-- **`eq:fraiture-first-window` from `eq:fraiture-large-window`, with no exact prime sum**:
`N ≥ 105 000 001` is covered by the large window; below it, `cover_below_large` and
`mem_R_of_cover`.

**Remaining hypothesis:** `Eq_FraitureLargeWindow`. -/
theorem eq_FraitureFirstWindow_of_large (hL : Principia.Erdos1054.Eq_FraitureLargeWindow) :
    Principia.Erdos1054.Eq_FraitureFirstWindow := by
  intro N hN1 hN2
  by_cases hN : 105000001 ≤ N
  · exact hL N hN (le_trans hN2 (by norm_num))
  · exact mem_R_of_cover N (by omega) (cover_below_large (N - 1) (by omega) (by omega))

end Principia.Erdos1054.Alt7.Window1
