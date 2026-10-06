/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
The five statement definitions in section (1) are transcribed from Hyunsik Chae's development
`hs-chae/pntpp` (https://github.com/hs-chae/pntpp, commit 35fa8a2,
`Pntpp/DivisorPrefix/Statement.lean`; identical in his Palomar repository hs-chae/erdos1054_hyunsik,
commit c065f37, Apache-2.0); only their statements are reproduced, none of his proofs.
-/
import Principia.Erdos1054.Alt7.FromAtoms896I

set_option autoImplicit false

/-!
# Hyunsik Chae's formalization of `thm:fraiture-representability`, connected to ours

Hyunsik Chae formalized the representability theorem `𝓡 = ℕ ∖ {2, 5}` first -- a formalization of
the divisor-prefix argument of Jimmy Fraiture's (JIF) Erdős 1054 verifier -- in `hs-chae/pntpp`
(Lean 4.29.1; later `hs-chae/erdos1054_hyunsik`, ported in `Chae/Pntpp/`, see its `CREDITS.md`): `Pntpp.DivisorPrefix.targetClassification_of_helfgott :
HelfgottTailHypothesis → TargetClassification`. His reduction is conditional on one explicit input,
`HelfgottTailHypothesis` (the balanced ternary Goldbach statement for odd `N ≥ 10^27`).

This module states his objects in his own words (section 1) and proves that they are OUR objects:
* `prefixDivisorSum_eq` -- his `prefixDivisorSum` is our `prefixSumDivisors`, by `rfl`;
* `represents_iff` -- his `Represents n` is our `n ∈ R`;
* `helfgottTail_iff` -- his `HelfgottTailHypothesis` is our `Lem_FraitureBalancedGoldbach`
  (`lem:fraiture-balanced-goldbach`), up to the order of the premises and of the sum;
* `targetClassification_iff` -- his `TargetClassification` is our `Eq_ExactRepresentability`.

and then closes BOTH his input and his conclusion from our Helfgott chain:
`chae_atoms896I` derives `HelfgottTailHypothesis ∧ TargetClassification` from exactly the 41
cited inputs of `FromAtoms896I.ep1054_atoms896I` (18 cited machine computations, 23 cited
published theorems). So the hypothesis his reduction carries is discharged by our formalization
of Helfgott's argument.

`Principia/Erdos1054/Chae/` is reserved for Hyunsik Chae's route: the port of his own lemmas
(credited to him) is added as further modules beside this one.
-/

namespace Principia.Erdos1054.Chae

open Principia.Erdos1054 Principia.Common.TernaryGoldbach

/-! ## (1) Hyunsik Chae's statements (transcribed; `@[blueprint]` attributes dropped) -/

/-- (Chae) The divisors of a positive integer, listed in increasing order. -/
noncomputable def divisorList (m : ℕ) : List ℕ :=
  (Nat.divisors m).sort (· ≤ ·)

/-- (Chae) The sum of the first `k` divisors of `m` in increasing order. -/
noncomputable def prefixDivisorSum (m k : ℕ) : ℕ :=
  ((divisorList m).take k).sum

/-- (Chae) `n` is the sum of a nonempty initial segment of the increasing divisor list of some
positive integer `m`. -/
def Represents (n : ℕ) : Prop :=
  ∃ m k : ℕ,
    0 < m ∧
    0 < k ∧
    k ≤ (divisorList m).length ∧
    prefixDivisorSum m k = n

/-- (Chae) The target classification: exactly `2` and `5` fail to be represented. -/
abbrev TargetClassification : Prop :=
  ∀ n : ℕ, 0 < n → (Represents n ↔ n ≠ 2 ∧ n ≠ 5)

/-- (Chae) The explicit external input used for the tail: every odd `N ≥ 10^27` is a sum of three
distinct odd primes, each larger than `N / (30000 log N)`. -/
def HelfgottTailHypothesis : Prop :=
  ∀ N : ℕ,
    10 ^ 27 ≤ N →
    Odd N →
    ∃ p q r : ℕ,
      p.Prime ∧ q.Prime ∧ r.Prime ∧
      Odd p ∧ Odd q ∧ Odd r ∧
      p ≠ q ∧ p ≠ r ∧ q ≠ r ∧
      N = p + q + r ∧
      (N : ℝ) / (30000 * Real.log N) < (p : ℝ) ∧
      (N : ℝ) / (30000 * Real.log N) < (q : ℝ) ∧
      (N : ℝ) / (30000 * Real.log N) < (r : ℝ)

/-! ## (2) His objects are ours -/

/-- His prefix sum is our `prefixSumDivisors`, definitionally. -/
theorem prefixDivisorSum_eq (m k : ℕ) : prefixDivisorSum m k = prefixSumDivisors m k := rfl

/-- His `Represents n` is our `n ∈ R`. -/
theorem represents_iff (n : ℕ) : Represents n ↔ n ∈ R := by
  constructor
  · rintro ⟨m, k, hm, hk, hkl, hsum⟩
    refine ⟨m, hm, k, hk, ?_, ?_⟩
    · simpa [divisorList, Finset.length_sort] using hkl
    · rw [← hsum]
      rfl
  · rintro ⟨m, hm, k, hk, hkc, hN⟩
    refine ⟨m, k, hm, hk, ?_, ?_⟩
    · simpa [divisorList, Finset.length_sort] using hkc
    · rw [hN]
      rfl

/-- His `HelfgottTailHypothesis` is our `lem:fraiture-balanced-goldbach`. -/
theorem helfgottTail_iff : HelfgottTailHypothesis ↔ Lem_FraitureBalancedGoldbach := by
  constructor
  · intro h H hodd hH
    obtain ⟨p, q, r, hp, hq, hr, op, oq, or_, hpq, hpr, hqr, hsum, h1, h2, h3⟩ := h H hH hodd
    exact ⟨p, q, r, hp, hq, hr, op, oq, or_, hpq, hpr, hqr, hsum.symm, h1, h2, h3⟩
  · intro h N hN hodd
    obtain ⟨p, q, r, hp, hq, hr, op, oq, or_, hpq, hpr, hqr, hsum, h1, h2, h3⟩ := h N hodd hN
    exact ⟨p, q, r, hp, hq, hr, op, oq, or_, hpq, hpr, hqr, hsum.symm, h1, h2, h3⟩

/-- His `TargetClassification` is our `eq:exact-representability`. -/
theorem targetClassification_iff : TargetClassification ↔ Eq_ExactRepresentability := by
  change TargetClassification ↔ R = {N : ℕ | 1 ≤ N ∧ N ≠ 2 ∧ N ≠ 5}
  have h0 : 0 ∉ R := by
    rintro ⟨m, hm, k, hk, -, hN⟩
    have hsum : 0 < prefixSumDivisors m k := by
      unfold prefixSumDivisors
      have hne : m.divisors.sort (· ≤ ·) ≠ [] := by
        intro h
        have := congrArg List.length h
        rw [Finset.length_sort] at this
        exact (Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr (by omega)⟩).ne' this
      obtain ⟨a, l, hal⟩ := List.exists_cons_of_ne_nil hne
      have ha : a ∈ m.divisors := by
        rw [← Finset.mem_sort (· ≤ ·), hal]
        exact List.mem_cons_self
      have hapos : 0 < a := Nat.pos_of_mem_divisors ha
      rw [hal]
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      simp only [List.take_succ_cons, List.sum_cons]
      omega
    omega
  constructor
  · intro h
    ext N
    simp only [Set.mem_setOf_eq]
    by_cases hN : N = 0
    · subst hN
      exact ⟨fun hm => (h0 hm).elim, fun hm => by omega⟩
    · have := h N (Nat.pos_of_ne_zero hN)
      rw [represents_iff] at this
      rw [this]
      omega
  · intro h n hn
    rw [represents_iff, h]
    simp only [Set.mem_setOf_eq]
    omega

/-! ## (3) His input and his conclusion, closed by our Helfgott chain -/

/-- **Hyunsik Chae's theorem with its hypothesis discharged**: his `HelfgottTailHypothesis` and his
`TargetClassification`, from exactly the 41 cited inputs of `FromAtoms896I.ep1054_atoms896I`.
Application only. -/
theorem chae_atoms896I (p : PC.PlattThm71) (z : PC.PlattTrudgian)
    (chk : HC.EspagnCheckCited) (sm : HC.EspagnSmallCited) (ch : HC.CharpyCited)
    (cp : HX.CharpasCited) (gr : HC.AusteriaGridCited) (mc : HC.MalMainCited)
    (am : HC.AmanitaBisectCited) (ab : HC.AppBCited) (cg : HC.CameloGridCited)
    (wo : HC.WollustCited) (kc : HC.KastCited) (hn : HC.NotungCited)
    (cs : HC.CortoSmallCited) (ys : HC.YuttoSmallCited) (c0 : HC.CortoC0Cited)
    (hRc : HC.RamareCited)
    (hZC : HM.ZeroCount) (rs : HX.RS75Theta) (cer : CY.CERange) (hm : CY.Malito)
    (hc : CY.Cante) (h15 : GS.RS62Thm15) (h12 : EB.RS62Thm12) (h13 : EB.RS62Thm13)
    (h316 : LQ.RS62_316) (h324 : LQ.RS62_324) (h330 : LQ.RS62_330) (h332 : LQ.RS62_332)
    (hR : EF.RosserL17) (hRS : EF.RamareSaouterL2)
    (hgr : MPc.Grara) (hro : MPc.Ronsard) (hme : MPc.Meproz) (r75 : KLR.RS75Cor2)
    (ls : T2K.LargeSieve) (mi : T2M.MontgomeryIneq) (hMk : M2Y.RamareMarraki)
    (mv : T2G.MVWeighted) (mv8 : T2V.MV8Large) :
    HelfgottTailHypothesis ∧ TargetClassification := by
  have d := Alt7.FromAtoms896I.ep1054_atoms896I p z chk sm ch cp gr mc am ab cg wo kc hn cs ys
    c0 hRc hZC rs cer hm hc h15 h12 h13 h316 h324 h330 h332 hR hRS hgr hro hme r75 ls mi hMk mv
    mv8
  exact ⟨helfgottTail_iff.mpr d.c_Lem_FraitureBalancedGoldbach,
    targetClassification_iff.mpr d.c_Eq_ExactRepresentability⟩

end Principia.Erdos1054.Chae
