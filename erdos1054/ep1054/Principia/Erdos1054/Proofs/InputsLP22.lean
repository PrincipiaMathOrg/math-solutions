/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Erdos1054.Statements.Inputs
import Principia.Erdos1054.Density
import Principia.Common.LucaPomerance.SquareDivisor

set_option autoImplicit false

/-!
# EP1054: the Luca–Pomerance Lemma 2.2 input, discharged

Discharges `Principia.Erdos1054.Cite_LP_Lemma22_range` (paper
`Campaigns/Erdos-1054/collab-paper/EP1054.tex`, `lem:LP-inputs`, lines 1326–1330): off a
density-zero set, if `n` has a prime factor `p > n^{7/9}`, then no prime `q₀` with
`y(n) < q₀ ≤ n^{10/27}` has `q₀² ∣ s(n)`.

The exceptional set is the set of violators itself. Its density is zero because
* `y(n) = log log n / log log log n → ∞` (`yLP_eventually_gt`), so past some `N₀(K)` every
  violator is an exception of level `K` in the sense of `Common.LucaPomerance.LP22Bad`, and
* at level `K` there are at most `54216 X / K` of those up to `X`
  (`Common.LucaPomerance.card_LP22Bad_le`: Brun–Titchmarsh in the class that `q₀² ∣ p s(m) + σ(m)`
  forces on `p`, modulo `q₀²/gcd(q₀², s(m))`).

No other input is used: in particular **not** `Cite_LP_Lemma21`, which Luca–Pomerance's own proof
of their Lemma 2.2 invokes (their case `π ∣ s(m)`). See `Campaigns/Erdos-1054/LP22-POLLACK-PLAN.md`.
-/

namespace Principia.Erdos1054.Proofs.InputsLP22

open Finset Principia.Common.LucaPomerance.LP22

/-- `y(n) = log log n / log log log n` exceeds any `K` for all large `n`. -/
theorem yLP_eventually_gt (K : ℝ) : ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → K < yLP n := by
  set T : ℝ := 4 * K ^ 2 + 4 with hT
  refine ⟨⌈Real.exp (Real.exp T)⌉₊, fun n hn => ?_⟩
  have hnR : Real.exp (Real.exp T) ≤ (n : ℝ) := (Nat.ceil_le).1 hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le (Real.exp_pos _) hnR
  have hlogn : Real.exp T ≤ Real.log n := by
    have := Real.log_le_log (Real.exp_pos _) hnR
    rwa [Real.log_exp] at this
  have hL : T ≤ Real.log (Real.log n) := by
    have := Real.log_le_log (Real.exp_pos _) hlogn
    rwa [Real.log_exp] at this
  set L := Real.log (Real.log n) with hLdef
  have hT4 : 4 ≤ T := by nlinarith [sq_nonneg K]
  have hL4 : 4 ≤ L := le_trans hT4 hL
  have hy : yLP n = L / Real.log L := rfl
  rw [hy]
  have hL0 : 0 < L := by linarith
  have hlogL0 : 0 < Real.log L := Real.log_pos (by linarith)
  have hs0 : 0 < Real.sqrt L := Real.sqrt_pos.2 hL0
  have hss : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hL0.le
  have hlogL : Real.log L < 2 * Real.sqrt L := by
    have h1 : Real.log (Real.sqrt L) = Real.log L / 2 := Real.log_sqrt hL0.le
    have h2 : Real.log (Real.sqrt L) ≤ Real.sqrt L - 1 := Real.log_le_sub_one_of_pos hs0
    linarith
  have hK : 2 * K < Real.sqrt L := by
    rcases lt_or_ge K 0 with hK0 | hK0
    · linarith
    · rw [Real.lt_sqrt (by linarith)]
      nlinarith
  rw [lt_div_iff₀ hlogL0]
  rcases lt_or_ge K 0 with hK0 | hK0
  · nlinarith
  · calc K * Real.log L ≤ K * (2 * Real.sqrt L) := mul_le_mul_of_nonneg_left hlogL.le hK0
      _ = 2 * K * Real.sqrt L := by ring
      _ < Real.sqrt L * Real.sqrt L := mul_lt_mul_of_pos_right hK hs0
      _ = L := hss

/-- The violators of `Cite_LP_Lemma22_range`. -/
def lp22Exceptions : Set ℕ :=
  {n | (∃ p ∈ n.primeFactors, (n : ℝ) ^ ((7 : ℝ) / 9) < (p : ℝ)) ∧
    ∃ q₀ : ℕ, q₀.Prime ∧ yLP n < (q₀ : ℝ) ∧ (q₀ : ℝ) ≤ (n : ℝ) ^ ((10 : ℝ) / 27) ∧
      q₀ ^ 2 ∣ aliquot n}

open Classical in
/-- The violators have density zero. -/
theorem densZero_lp22Exceptions : DensZero lp22Exceptions := by
  rw [densZero_iff_exists_real]
  intro ε hε
  set K : ℕ := ⌈2 * 54216 / ε⌉₊ + 1 with hKdef
  have hK1 : 1 ≤ K := by omega
  have hKR : 2 * 54216 / ε ≤ (K : ℝ) := by
    have := Nat.le_ceil (2 * 54216 / ε)
    rw [hKdef]
    push_cast
    linarith
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK1
  obtain ⟨N₀, hN₀⟩ := yLP_eventually_gt (K : ℝ)
  refine ⟨max (Real.exp 9) (2 * N₀ / ε), fun X hX => ?_⟩
  have hX9 : Real.exp 9 ≤ X := le_trans (le_max_left _ _) hX
  have hXN : 2 * N₀ / ε ≤ X := le_trans (le_max_right _ _) hX
  have hX0 : 0 < X := lt_of_lt_of_le (Real.exp_pos 9) hX9
  have hsub : (Icc 1 ⌊X⌋₊).filter (· ∈ lp22Exceptions) ⊆
      (Icc 1 ⌊X⌋₊).filter (· < N₀) ∪ (Icc 1 ⌊X⌋₊).filter (LP22Bad K) := by
    intro n hn
    obtain ⟨hnI, hnE⟩ := Finset.mem_filter.1 hn
    rw [Finset.mem_union]
    rcases lt_or_ge n N₀ with hlt | hge
    · exact Or.inl (Finset.mem_filter.2 ⟨hnI, hlt⟩)
    · right
      refine Finset.mem_filter.2 ⟨hnI, ?_⟩
      obtain ⟨hp, q₀, hq, hyq, hqn, hdvd⟩ := hnE
      have hKq : (K : ℝ) < q₀ := lt_trans (hN₀ n hge) hyq
      exact ⟨hp, q₀, hq, by exact_mod_cast hKq, hqn, hdvd⟩
  have hsmall : ((Icc 1 ⌊X⌋₊).filter (· < N₀)).card ≤ N₀ := by
    calc ((Icc 1 ⌊X⌋₊).filter (· < N₀)).card ≤ (Finset.range N₀).card := by
          apply Finset.card_le_card
          intro n hn
          exact Finset.mem_range.2 (Finset.mem_filter.1 hn).2
      _ = N₀ := Finset.card_range N₀
  have hbig := card_LP22Bad_le K hK1 X hX9
  have hcnt : (cnt lp22Exceptions X : ℝ) ≤ N₀ + 54216 * X / K := by
    unfold cnt
    have h1 := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have h2 : ((((Icc 1 ⌊X⌋₊).filter (· ∈ lp22Exceptions)).card : ℕ) : ℝ) ≤
        (((Icc 1 ⌊X⌋₊).filter (· < N₀)).card : ℝ) +
          (((Icc 1 ⌊X⌋₊).filter (LP22Bad K)).card : ℝ) := by exact_mod_cast h1
    have h3 : (((Icc 1 ⌊X⌋₊).filter (· < N₀)).card : ℝ) ≤ N₀ := by exact_mod_cast hsmall
    linarith
  have hA : 54216 * X / K ≤ ε / 2 * X := by
    rw [div_le_iff₀ hKpos]
    have : 2 * 54216 ≤ ε * K := by
      have := mul_le_mul_of_nonneg_left hKR hε.le
      rwa [mul_div_cancel₀ _ hε.ne'] at this
    nlinarith
  have hB : (N₀ : ℝ) ≤ ε / 2 * X := by
    have := mul_le_mul_of_nonneg_left hXN hε.le
    rw [mul_div_cancel₀ _ hε.ne'] at this
    linarith
  linarith

end Principia.Erdos1054.Proofs.InputsLP22

namespace Principia.Erdos1054.Proofs

/-- **`Cite_LP_Lemma22_range`**, discharged: Brun–Titchmarsh (`C = 2008`) and `y(n) → ∞`, with no
appeal to `Cite_LP_Lemma21`. -/
theorem input_Cite_LP_Lemma22_range : Principia.Erdos1054.Cite_LP_Lemma22_range :=
  ⟨InputsLP22.lp22Exceptions, InputsLP22.densZero_lp22Exceptions,
    fun _ hn hp q₀ hq hy hq' hdvd => hn ⟨hp, q₀, hq, hy, hq', hdvd⟩⟩

end Principia.Erdos1054.Proofs
