/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.BalancedGoldbach.Balanced
import Principia.Erdos1054.Alt.Round4

set_option autoImplicit false

/-!
# EP1054: `𝓡` has density one, unconditionally — Helfgott out of the §6–§7 headlines

`Alt.TailOnly` re-proved four headlines (`Prop_TightnessEquivalence` and the three §7 results)
from `RepDensityOne` (`ℕ ∖ 𝓡` has density zero) and reduced that statement to the even
unrepresented integers (`TailOnly.repDensityOne_iff_evenUnrep`); until now the only proof of it
went through `Cite_Helfgott_weighted` (every `n ≥ 10^27 + 10^8` is represented). This module proves
it outright.

**The construction.** For primes `3 < p < q < 3p`, the divisors of `m = 3pq` in increasing order
begin `1, 3, p, q` (the next is `3p > q`; `3q` and `pq` exceed `3p`), so the divisor-prefix sum
ending at `q` is `F(3p, q) = 4 + p + q` (`F_three_mul_prime`) and `4 + p + q ∈ 𝓡`
(`add_four_mem_R_of_balRep`). So an even `m ≥ 16` outside `𝓡` has `m − 4` even with no balanced
Goldbach representation `m − 4 = p + q`, `3 < p < q < 3p`.

**The analytic input** is `Principia.Common.BalancedGoldbach.balanced_goldbach`: almost every even
number has such a representation, unconditionally. It is the ported circle method read on the upper
half `N < n < 2N` of its own window, where the pair count is balanced for free (see that module).

**Results.**

* `evenUnrep_densZero` — the even integers outside `𝓡` have density zero;
* `repDensityOne_unconditional : Alt.TailOnly.RepDensityOne` — **no hypothesis**;
* `ep1054_Prop_TightnessEquivalence_unconditional` and
  `coverage_Rem_T_iff_Conj_unconditional` — **no hypothesis** (round 4: `Cite_Helfgott_weighted`);
* `ep1054_Thm_DaddUniversalSingularity_r5`, `ep1054_Cor_DaddHeavyTails_r5`,
  `ep1054_Prop_DaddCollisionCriterion_r5` — **`Cite_Erdos_singular` only** (round 4: Helfgott and
  `Cite_Erdos_singular`).

Helfgott now reaches EP1054 only through the Fraiture/classification rows (`Prop_FraitureTail`,
`Lem_FraitureBalancedGoldbach`, `Thm_FraitureRepresentability`, `Eq_ExactRepresentability` and its
restatements), which need *every* large integer, not almost every one.
-/

namespace Principia.Erdos1054.Alt5

open Principia.Erdos1054 Principia.Erdos1054.Spine Principia.Erdos1054.Proofs
open Principia.Common.BalancedGoldbach (BalRep notBalanced)

/-! ## 1. The divisor-prefix construction -/

/-- **The divisors of `3pq` up to `q` are `1, 3, p, q`.** For primes `3 < p < q < 3p`,
`F(3p, q) = 1 + 3 + p + q`. -/
theorem F_three_mul_prime (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (h3p : 3 < p) (hpq : p < q)
    (hq3 : q < 3 * p) : F (3 * p) q = 4 + p + q := by
  have hdiv : ((3 * p) * q).divisors.filter (· ≤ q) = {1, 3, p, q} := by
    ext t
    rw [Finset.mem_filter, Nat.mem_divisors]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hdvd, -⟩, hle⟩
      obtain ⟨y, z, hy, hz, rfl⟩ := Nat.dvd_mul.mp hdvd
      obtain ⟨u, v, hu, hv, rfl⟩ := Nat.dvd_mul.mp hy
      have hp2 := hp.two_le
      have hq2 := hq.two_le
      rcases (Nat.dvd_prime Nat.prime_three).mp hu with rfl | rfl <;>
      rcases (Nat.dvd_prime hp).mp hv with rfl | rfl <;>
      rcases (Nat.dvd_prime hq).mp hz with rfl | rfl
      all_goals first
        | omega
        | (exfalso; nlinarith)
    · have hp2 := hp.two_le
      have hne : 3 * p * q ≠ 0 := (Nat.mul_pos (Nat.mul_pos (by norm_num) hp.pos) hq.pos).ne'
      rintro (rfl | rfl | rfl | rfl)
      · exact ⟨⟨one_dvd _, hne⟩, by omega⟩
      · exact ⟨⟨⟨p * q, by ring⟩, hne⟩, by omega⟩
      · exact ⟨⟨⟨3 * q, by ring⟩, hne⟩, by omega⟩
      · exact ⟨⟨⟨3 * p, by ring⟩, hne⟩, le_refl _⟩
  unfold F
  rw [hdiv, Finset.sum_insert (by simp; omega), Finset.sum_insert (by simp; omega),
    Finset.sum_insert (by simp; omega), Finset.sum_singleton]
  omega

/-- **A balanced Goldbach representation of `n` puts `n + 4` in `𝓡`**: `n = p + q` with primes
`3 < p < q < 3p` gives `n + 4 = F(3p, q)`. -/
theorem add_four_mem_R_of_balRep {n : ℕ} (h : BalRep n) : n + 4 ∈ R := by
  obtain ⟨p, q, hp, hq, h3p, hpq, hq3, rfl⟩ := h
  rw [mem_R_iff_exists_F]
  refine ⟨3 * p, q, by omega, hq.one_lt.le, ?_⟩
  rw [F_three_mul_prime p q hp hq h3p hpq hq3]
  omega

/-! ## 2. Density bookkeeping -/

/-- Shifting a set up by `k` does not increase its counting function. -/
theorem cnt_shift_le (S : Set ℕ) (k : ℕ) (X : ℝ) :
    cnt {m : ℕ | k < m ∧ m - k ∈ S} X ≤ cnt S X := by
  unfold cnt
  apply Finset.card_le_card_of_injOn (fun m => m - k)
  · intro m hm
    rw [Finset.mem_coe, mem_cntFinset] at hm
    rw [Finset.mem_coe, mem_cntFinset]
    obtain ⟨⟨h1, h2⟩, hk, hS⟩ := hm
    dsimp only
    exact ⟨⟨by omega, by omega⟩, hS⟩
  · intro a ha b hb hab
    rw [Finset.mem_coe, mem_cntFinset] at ha hb
    have h1 := ha.2.1
    have h2 := hb.2.1
    dsimp only at hab
    omega

/-- A density-zero set stays density zero when shifted up by `k`. -/
theorem densZero_shift {S : Set ℕ} (k : ℕ) (h : DensZero S) :
    DensZero {m : ℕ | k < m ∧ m - k ∈ S} := by
  rw [densZero_iff_eventually_le] at h ⊢
  intro ε hε
  filter_upwards [h ε hε] with n hn
  exact le_trans (by exact_mod_cast cnt_shift_le S k (n : ℝ)) hn

/-- **Almost-all balanced Goldbach in `Defs.DensZero` form**: the even `n` with no representation
`n = p + q`, primes `3 < p < q < 3p`, have density zero. -/
theorem densZero_notBalanced : DensZero {n : ℕ | notBalanced n} :=
  Alt.densZero_of_densityZero notBalanced Principia.Common.BalancedGoldbach.balanced_goldbach

/-! ## 3. Density one of `𝓡` -/

/-- **The even integers outside `𝓡` have density zero, unconditionally.** An even `m ≥ 16` outside
`𝓡` has `m − 4` even and not balanced (`add_four_mem_R_of_balRep`); those `m` are the shift by `4`
of the balanced exceptions (`densZero_notBalanced`), and `m < 16` is finite. -/
theorem evenUnrep_densZero : DensZero {n : ℕ | Even n ∧ n ∉ R} := by
  have h1 : DensZero {m : ℕ | 4 < m ∧ m - 4 ∈ {n : ℕ | notBalanced n}} :=
    densZero_shift 4 densZero_notBalanced
  have h2 : DensZero {m : ℕ | m < 16} := densZero_of_finite (Set.finite_lt_nat 16)
  refine densZero_subset (densZero_union h2 h1) ?_
  rintro m ⟨he, hm⟩
  by_cases h16 : m < 16
  · exact Or.inl h16
  · right
    refine ⟨by omega, ?_, ?_⟩
    · obtain ⟨k, hk⟩ := he
      exact ⟨k - 2, by omega⟩
    · intro hb
      apply hm
      have h := add_four_mem_R_of_balRep hb
      rwa [show m - 4 + 4 = m by omega] at h

/-- **`𝓡` has density one — no hypothesis.** `TailOnly.repDensityOne_iff_evenUnrep` reduces it to
the even unrepresented integers (the odd half is almost-all binary Goldbach), and
`evenUnrep_densZero` supplies those. (Round 4: from `Cite_Helfgott_weighted`.) -/
theorem repDensityOne_unconditional : Alt.TailOnly.RepDensityOne :=
  Alt.TailOnly.repDensityOne_iff_evenUnrep.2 evenUnrep_densZero

/-! ## 4. The headlines that consumed density one -/

/-- **EP1054 `prop:tightness-equivalence`, unconditionally**
(`TailOnly.prop_TightnessEquivalence_of_repDensityOne` at `repDensityOne_unconditional`).

**Remaining hypotheses: none.** (Round 4, `Round4.ep1054_Prop_TightnessEquivalence_r4`:
`Cite_Helfgott_weighted`.) -/
theorem ep1054_Prop_TightnessEquivalence_unconditional : Prop_TightnessEquivalence :=
  Alt.TailOnly.prop_TightnessEquivalence_of_repDensityOne repDensityOne_unconditional

/-- **`eq:T` ⟺ the weak bounded-cofactor conjecture (`Coverage.Rem_T_iff_Conj`), unconditionally**
(`TailOnly.link_Coverage_Rem_T_iff_Conj_tailOnly` at `repDensityOne_unconditional`). A field of
`Spine.DerivedClaims`, not a headline.

**Remaining hypotheses: none.** (Round 4, `TailOnly.coverage_Rem_T_iff_Conj_tailOnly`:
`Cite_Helfgott_weighted`.) -/
theorem coverage_Rem_T_iff_Conj_unconditional : Coverage.Rem_T_iff_Conj :=
  Alt.TailOnly.link_Coverage_Rem_T_iff_Conj_tailOnly leaf_Coverage_Fact_RtPosIff
    repDensityOne_unconditional ep1054_Prop_TightnessEquivalence_unconditional

/-- **EP1054 `thm:dadd:universal-singularity`**
(`Round4.thm_DaddUniversalSingularity_of_repDensityOne_r4` at `repDensityOne_unconditional`).

**Remaining hypothesis:** `Cite_Erdos_singular`. (Round 4: `Cite_Helfgott_weighted` and
`Cite_Erdos_singular`.) -/
theorem ep1054_Thm_DaddUniversalSingularity_r5 (i_Cite_Erdos_singular : Cite_Erdos_singular) :
    Thm_DaddUniversalSingularity :=
  Alt.Round4.thm_DaddUniversalSingularity_of_repDensityOne_r4 repDensityOne_unconditional
    i_Cite_Erdos_singular

/-- **EP1054 heavy-tail corollary (`Cor_DaddHeavyTails`)**
(`Round4.cor_DaddHeavyTails_of_repDensityOne_r4` at `repDensityOne_unconditional`).

**Remaining hypothesis:** `Cite_Erdos_singular`. (Round 4: `Cite_Helfgott_weighted` and
`Cite_Erdos_singular`.) -/
theorem ep1054_Cor_DaddHeavyTails_r5 (i_Cite_Erdos_singular : Cite_Erdos_singular) :
    Cor_DaddHeavyTails :=
  Alt.Round4.cor_DaddHeavyTails_of_repDensityOne_r4 repDensityOne_unconditional
    i_Cite_Erdos_singular

/-- **EP1054 `prop:dadd:collision-criterion`**
(`Round4.prop_DaddCollisionCriterion_of_repDensityOne_r4` at `repDensityOne_unconditional`).

**Remaining hypothesis:** `Cite_Erdos_singular`. (Round 4: `Cite_Helfgott_weighted` and
`Cite_Erdos_singular`.) -/
theorem ep1054_Prop_DaddCollisionCriterion_r5 (i_Cite_Erdos_singular : Cite_Erdos_singular) :
    Prop_DaddCollisionCriterion :=
  Alt.Round4.prop_DaddCollisionCriterion_of_repDensityOne_r4 repDensityOne_unconditional
    i_Cite_Erdos_singular

end Principia.Erdos1054.Alt5
