/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Erdos1054.Proofs.ReprElementary
import Principia.Erdos1054.Alt6.Dusart.LargePrimeSum
import Principia.Common.KernelCert.Seed

set_option autoImplicit false

/-!
# `Comp_Verifier_largeSeed` removed: the large window of `prop:fraiture-finite`, unconditionally

The spine's `Link_Step_FraitureLargeWindowCover` (EP1054.tex lines 771–793) takes the verifier
check `Comp_Verifier_largeSeed` (every `N ∈ [1.05·10^8, 1.56·10^8]` is a sum of four or five
distinct primes of `(2·10^7, 4·10^7)`) and extends it prime by prime up to `3.99·10^14` by
`Lem_FraitureExtension`. Its base case uses only the subset-sum form of the check: each seed `N`
is the sum of *some* set of primes of `(2·10^7, 4·10^7]`.

* `step_FraitureLargeWindowCover_of_seedCover` is that link with its seed hypothesis stated in
  the subset-sum form, the smallest finite fact the argument uses. The proof is
  `Proofs.link_Step_FraitureLargeWindowCover` with the base case rewritten; the induction step is
  unchanged (`Lem_FraitureExtension` at `Proofs.leaf_Lem_FraitureExtension`, the width bound
  `Proofs.ReprElementary.large_width`).
* `Principia.Common.KernelCert.seed_cover` is that fact, kernel-checked (`decide +kernel`, no
  `ofReduceBool`), so `step_FraitureLargeWindowCover_unconditional` has no hypothesis.
* `eq_FraitureLargeWindow_unconditional` is the spine's `Link_Eq_FraitureLargeWindow` at it,
  `Alt6.Dusart.step_FraitureLargePrimeSum_unconditional` and `Proofs.leaf_Lem_FraiturePrimeWindow`.

`Principia.Common.KernelCert.seed_four_five` is moreover `Comp_Verifier_largeSeed` verbatim, so
the input itself is a theorem (`input_Comp_Verifier_largeSeed`), and the spine's own link applied
to it gives the same statement (`step_FraitureLargeWindowCover_via_link`). No statement is
weakened: every theorem's type is a spine `Prop`, or the spine's link with one hypothesis
replaced by its subset-sum form.

With the large window closed, `Prop_FraitureFinite` (#117) needs only `Comp_Verifier_small` and
`Comp_Verifier_window1` (`prop_FraitureFinite_of_small_window1`).

**SUPERSEDED, and this file alone would mislead you:** the sibling tasks closed both of those too,
so #117 is **unconditional** — `Alt7.Round7.ep1054_Prop_FraitureFinite_unconditional`.
`Alt7.Window1.input_Comp_Verifier_window1` proves the second input verbatim, and
`Comp_Verifier_small` is routed around by `Alt7.Small.eq_FraitureSmall_of_firstWindow`.
`prop_FraitureFinite_of_small_window1` below therefore has no consumer; it is kept as the record of
what this task closed on its own.

The intervals `(2·10^7, 4·10^7)` and `(2·10^7, 4·10^7]` carry the same primes, since `4·10^7` is
even; the proofs use the `Finset.Ioc` form throughout and nothing depends on the choice.
-/

namespace Principia.Erdos1054.Alt7.Large

open Principia.Erdos1054

/-- **`Comp_Verifier_largeSeed`, proved** (check 3 of the verifier): every
`N ∈ [105 000 000, 156 000 000]` is the sum of four or five distinct primes of
`(2·10^7, 4·10^7)`. `Principia.Common.KernelCert.seed_four_five`, whose type is the body of the
`Prop` verbatim.

**Remaining hypotheses: none.** -/
theorem input_Comp_Verifier_largeSeed : Principia.Erdos1054.Comp_Verifier_largeSeed :=
  Principia.Common.KernelCert.seed_four_five

/-- **The large-window cover from its seed** (EP1054.tex lines 771–793): if every integer of
`[105 000 000, 156 000 000]` is a sum of distinct primes of `(2·10^7, 4·10^7]`, then every
`N ∈ [105 000 000, 156 000 000 + ∑_{4·10^7 < p ≤ 3.99·10^14} p]` is a sum of distinct primes of
`(2·10^7, 3.99·10^14]`.

This is `Proofs.link_Step_FraitureLargeWindowCover` with `Comp_Verifier_largeSeed` replaced by its
subset-sum form (the base case of the induction uses nothing else) and `Lem_FraitureExtension`
supplied by `Proofs.leaf_Lem_FraitureExtension`. -/
theorem step_FraitureLargeWindowCover_of_seedCover
    (hSeed : ∀ N : ℕ, 105000000 ≤ N → N ≤ 156000000 →
      N ∈ subsetSums ((Finset.Ioc 20000000 40000000).filter Nat.Prime)) :
    Principia.Erdos1054.Step_FraitureLargeWindowCover := by
  have hExt : Lem_FraitureExtension := Proofs.leaf_Lem_FraitureExtension
  have key : ∀ n, 40000000 ≤ n → ∀ N, 105000000 ≤ N →
      N ≤ 156000000 + ∑ r ∈ (Finset.Ioc 40000000 n).filter Nat.Prime, r →
      N ∈ subsetSums ((Finset.Ioc 20000000 n).filter Nat.Prime) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
      intro N hN1 hN2
      rw [Finset.Ioc_self, Finset.filter_empty, Finset.sum_empty] at hN2
      exact hSeed N hN1 (by omega)
    | succ n hn ih =>
      intro N hN1 hN2
      rw [← Finset.insert_Ioc_right_eq_Ioc_add_one hn, Finset.filter_insert] at hN2
      rw [← Finset.insert_Ioc_right_eq_Ioc_add_one (by omega : 20000000 ≤ n),
        Finset.filter_insert]
      by_cases hp : (n + 1).Prime
      · rw [if_pos hp] at hN2 ⊢
        have hnotin : n + 1 ∉ (Finset.Ioc 40000000 n).filter Nat.Prime := by simp
        rw [Finset.sum_insert hnotin] at hN2
        have hw := Proofs.ReprElementary.large_width n hn
        exact hExt 105000000 (156000000 + ∑ r ∈ (Finset.Ioc 40000000 n).filter Nat.Prime, r) _
          (n + 1) (by omega) (fun q hq => (Finset.mem_filter.1 hq).2) ih hp (by simp)
          (by omega) N hN1 (by omega)
      · rw [if_neg hp] at hN2 ⊢
        exact ih N hN1 hN2
  intro N hN1 hN2
  exact key 399000000000000 (by norm_num) N hN1 hN2

/-- **EP1054 `Step_FraitureLargeWindowCover`, unconditionally** (lines 771–793): every
`N ∈ [105 000 000, 156 000 000 + ∑_{4·10^7 < p ≤ 3.99·10^14} p]` is a sum of distinct primes of
`(2·10^7, 3.99·10^14]`. `step_FraitureLargeWindowCover_of_seedCover` at the kernel-checked seed
`Principia.Common.KernelCert.seed_cover`.

**Remaining hypotheses: none.** (Rounds 1–6: `Comp_Verifier_largeSeed`.) -/
theorem step_FraitureLargeWindowCover_unconditional :
    Principia.Erdos1054.Step_FraitureLargeWindowCover :=
  step_FraitureLargeWindowCover_of_seedCover Principia.Common.KernelCert.seed_cover

/-- The same statement by the spine's own link: `Proofs.link_Step_FraitureLargeWindowCover`
at `Proofs.leaf_Lem_FraitureExtension` and `input_Comp_Verifier_largeSeed`. A cross-check that the
re-route proves exactly what the link does.

**Remaining hypotheses: none.** -/
theorem step_FraitureLargeWindowCover_via_link :
    Principia.Erdos1054.Step_FraitureLargeWindowCover :=
  Proofs.link_Step_FraitureLargeWindowCover Proofs.leaf_Lem_FraitureExtension
    input_Comp_Verifier_largeSeed

/-- **`Link_Step_FraitureLargeWindowCover` without its inputs**: the link's conclusion holds
outright, so neither `Lem_FraitureExtension` nor `Comp_Verifier_largeSeed` is used through it. -/
theorem link_Step_FraitureLargeWindowCover_unconditional :
    Principia.Erdos1054.Spine.Link_Step_FraitureLargeWindowCover :=
  fun _ _ => step_FraitureLargeWindowCover_unconditional

/-- **EP1054 `eq:fraiture-large-window` (`Eq_FraitureLargeWindow`), unconditionally**
(lines 734–735, 771–823): every integer of `[105 000 001, 10^27 + 10^8]` lies in `𝓡`. The spine's
`Proofs.link_Eq_FraitureLargeWindow` at `step_FraitureLargeWindowCover_unconditional`,
`Alt6.Dusart.step_FraitureLargePrimeSum_unconditional` and `Proofs.leaf_Lem_FraiturePrimeWindow`.

**Remaining hypotheses: none.** (Round 6: `Comp_Verifier_largeSeed`. Rounds 1–5: that and
`Cite_Dusart_Thm69`.) -/
theorem eq_FraitureLargeWindow_unconditional : Principia.Erdos1054.Eq_FraitureLargeWindow :=
  Proofs.link_Eq_FraitureLargeWindow step_FraitureLargeWindowCover_unconditional
    Principia.Erdos1054.Alt6.Dusart.step_FraitureLargePrimeSum_unconditional
    Proofs.leaf_Lem_FraiturePrimeWindow

/-- **EP1054 `prop:fraiture-finite` (`Prop_FraitureFinite`, #117)** with the large window
unconditional: every integer of `[6, 10^7]`, `[469616, 273803744799154]` and
`[105000001, 10^27 + 10^8]` lies in `𝓡`. `Alt6.Round6.ep1054_Prop_FraitureFinite_r6`'s
composition (the spine's `spine_Prop_FraitureFinite`) with its third component replaced by
`eq_FraitureLargeWindow_unconditional`.

**Remaining hypotheses:** `Comp_Verifier_small`, `Comp_Verifier_window1`. (Round 6: those two and
`Comp_Verifier_largeSeed`.) **Superseded and unconsumed** — both remaining inputs were closed by the
sibling tasks, so use `Alt7.Round7.ep1054_Prop_FraitureFinite_unconditional`, which has none. -/
theorem prop_FraitureFinite_of_small_window1
    (i_Comp_Verifier_small : Comp_Verifier_small)
    (i_Comp_Verifier_window1 : Comp_Verifier_window1) :
    Principia.Erdos1054.Prop_FraitureFinite :=
  And.intro
    (Proofs.link_Eq_FraitureSmall Proofs.leaf_Step_FraitureSmallBq Proofs.leaf_Step_FraitureSeven
      i_Comp_Verifier_small)
    (And.intro
      (Proofs.link_Eq_FraitureFirstWindow
        (Proofs.link_Step_FraitureFirstWindowCover Proofs.leaf_Lem_FraitureExtension
          i_Comp_Verifier_window1)
        Proofs.leaf_Lem_FraiturePrimeWindow)
      eq_FraitureLargeWindow_unconditional)

end Principia.Erdos1054.Alt7.Large
