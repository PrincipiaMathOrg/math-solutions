/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.KernelCert.Sieve
import Principia.Erdos1054.Basic
import Principia.Erdos1054.Statements.S3_Repr

set_option autoImplicit false

/-!
# The small window of `prop:fraiture-finite`: the marking, as a kernel-checkable `Bool`

EP1054 lines 746–755 mark an integer `N` when `N = σ(B) + q ∑_{i ≤ j} d_i(B)` with
`1 ≤ B ≤ 1000`, `q > B` prime and `1 ≤ j ≤ τ(B)` (`smallSieveMarked`, the existential of
`Comp_Verifier_small`); `Step_FraitureSmallBq` says every marked integer is represented
(`mem_R_of_marked`). This file turns "every `N` of `[lo, hi]` other than `7` is marked" into one
`Bool`, `smallChk`, and proves it sound (`marked_of_smallChk`).

* **Prefix sums through a divisor.** A prefix `∑_{i ≤ j} d_i(B)` is `Fdiv B d` for its last
  divisor `d` (`Basic.Fdiv_eq_prefixSumDivisors`), and `Fdiv B d` is computed by `dsum B d`, an
  explicit `Nat.rec` over `e = 1, …, d` adding `e` when `B % e = 0` (`dsum_eq_Fdiv`); in
  particular `σ(B) = dsum B B` (`sig_eq_dsum`).
* **`j = 1` in bulk.** Then the prefix is `1` and `N = σ(B) + q`. For a prime bitset `P`,
  `shiftAbove P B σ(B)` is the bitset `{σ(B) + q : q ∈ P, q > B}` (one right and one left
  shift, kernel-native), and `markJ1 P Bs` is its union over a list `Bs`.
* **`j ≥ 2` one at a time.** A witness `(B, d, q)` stands for `σ(B) + q · Fdiv B d`; `okW`
  checks `1 ≤ B ≤ 1000`, `B < q`, `d ∣ B` and bit `q` of `P`, and `markW` sets the witnessed bits.
* `smallChk P Bs Ws lo hi` asks that every bit of `[lo, hi]` be set in
  `markJ1 P Bs ||| markW Ws ||| 2^7` and that every entry pass its test. With `P = primeBits L`
  (`KernelCert.testBit_primeBits`), a set bit other than `7` is a marked integer.

Nothing here is specific to a range; the data and the certificate are in `Cert.lean`.
-/

namespace Principia.Erdos1054.Alt7.Small

open Finset Principia.Erdos1054 Principia.Common.KernelCert

/-! ## 1. Divisor sums by structural recursion -/

/-- `dsum B d = ∑ {e : 1 ≤ e ≤ d, e ∣ B}`, by explicit `Nat.rec` (the kernel unfolds it one step
per `e`, all arithmetic native). -/
def dsum (B : ℕ) : ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0
    (fun k acc => Nat.add acc (bif B % (k + 1) == 0 then k + 1 else 0))

theorem dsum_zero (B : ℕ) : dsum B 0 = 0 := rfl

theorem dsum_succ (B k : ℕ) :
    dsum B (k + 1) = dsum B k + (bif B % (k + 1) == 0 then k + 1 else 0) := rfl

theorem Fdiv_zero (B : ℕ) : Fdiv B 0 = 0 := by
  unfold Fdiv
  refine Finset.sum_eq_zero (fun q hq => ?_)
  rw [Finset.mem_filter] at hq
  omega

theorem Fdiv_succ (B k : ℕ) (hB : 1 ≤ B) :
    Fdiv B (k + 1) = Fdiv B k + (bif B % (k + 1) == 0 then k + 1 else 0) := by
  unfold Fdiv
  have hsplit : B.divisors.filter (· ≤ k + 1) =
      B.divisors.filter (· ≤ k) ∪ B.divisors.filter (· = k + 1) := by
    ext q
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro ⟨h1, h2⟩
      rcases Nat.lt_or_ge q (k + 1) with h | h
      · exact Or.inl ⟨h1, by omega⟩
      · exact Or.inr ⟨h1, by omega⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨h1, by omega⟩
      · exact ⟨h1, by omega⟩
  have hdisj : Disjoint (B.divisors.filter (· ≤ k)) (B.divisors.filter (· = k + 1)) := by
    rw [Finset.disjoint_filter]
    intro q _ h1 h2
    omega
  rw [hsplit, Finset.sum_union hdisj]
  congr 1
  rw [Finset.sum_filter, Finset.sum_ite_eq']
  by_cases h : (k + 1) ∣ B
  · have hm : k + 1 ∈ B.divisors := Nat.mem_divisors.2 ⟨h, by omega⟩
    have h0 : B % (k + 1) = 0 := Nat.mod_eq_zero_of_dvd h
    rw [if_pos hm, h0]
    rfl
  · have hm : k + 1 ∉ B.divisors := fun hm => h (Nat.dvd_of_mem_divisors hm)
    have h0 : (B % (k + 1) == 0) = false := by
      rw [beq_eq_false_iff_ne]
      exact fun hc => h (Nat.dvd_of_mod_eq_zero hc)
    rw [if_neg hm, h0]
    rfl

/-- **`dsum` computes `Fdiv`** (the sum of the divisors of `B` up to `d`), for `B ≥ 1`. -/
theorem dsum_eq_Fdiv (B : ℕ) (hB : 1 ≤ B) : ∀ d, dsum B d = Fdiv B d
  | 0 => by rw [dsum_zero, Fdiv_zero]
  | k + 1 => by rw [dsum_succ, Fdiv_succ B k hB, dsum_eq_Fdiv B hB k]

theorem sig_eq_Fdiv (B : ℕ) : sig B = Fdiv B B := by
  unfold Fdiv
  rw [show sig B = ArithmeticFunction.sigma 1 B from rfl, ArithmeticFunction.sigma_one_apply,
    Finset.filter_true_of_mem]
  intro q hq
  exact Nat.divisor_le hq

/-- **`σ(B) = dsum B B`** for `B ≥ 1`. -/
theorem sig_eq_dsum (B : ℕ) (hB : 1 ≤ B) : sig B = dsum B B := by
  rw [sig_eq_Fdiv, dsum_eq_Fdiv B hB]

theorem dsum_one (B : ℕ) : dsum B 1 = 1 := by
  rw [dsum_succ, dsum_zero, Nat.mod_one]
  rfl

/-! ## 2. From a witness to a mark, and from a mark to `𝓡` -/

/-- A witness with its prefix written through its last divisor `d` is marked:
`σ(B) + q · Fdiv B d` is `σ(B) + q ∑_{i ≤ k} d_i(B)` at the prefix length `k` of `d`
(`Fdiv_eq_prefixSumDivisors`), for `1 ≤ B ≤ 1000`, `q > B` prime, `d ∣ B`. -/
theorem marked_of_Fdiv {B q d : ℕ} (hB1 : 1 ≤ B) (hB : B ≤ 1000) (hq : q.Prime) (hlt : B < q)
    (hd : d ∣ B) : smallSieveMarked (sig B + q * Fdiv B d) := by
  obtain ⟨k, hk1, hk2, hk⟩ :=
    Fdiv_eq_prefixSumDivisors B d (Nat.mem_divisors.2 ⟨hd, by omega⟩)
  exact ⟨B, q, k, hB1, hB, hq, hlt, hk1, hk2, by rw [hk]⟩

/-- **A marked integer is represented** (`Step_FraitureSmallBq`, EP1054 lines 746–752). -/
theorem mem_R_of_marked (hBq : Step_FraitureSmallBq) {N : ℕ} (h : smallSieveMarked N) :
    N ∈ R := by
  obtain ⟨B, q, j, hB1, hB, hq, hlt, hj1, hj, rfl⟩ := h
  exact hBq B q j hB1 hB hq hlt hj1 hj

/-! ## 3. The bitsets -/

/-- `{σ + q : q ∈ P, q > B}` as a bitset: drop the bits `≤ B` of `P`, then shift by `σ`. -/
def shiftAbove (P B s : ℕ) : ℕ := (P >>> (B + 1)) <<< (B + 1 + s)

theorem testBit_shiftAbove {P B s N : ℕ} (h : (shiftAbove P B s).testBit N = true) :
    B + 1 + s ≤ N ∧ P.testBit (N - s) = true := by
  unfold shiftAbove at h
  rw [Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_eq, Nat.testBit_shiftRight] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨h1, ?_⟩
  have he : B + 1 + (N - (B + 1 + s)) = N - s := by omega
  rwa [he] at h2

/-- The `j = 1` marks: `⋃_{B ∈ Bs} {σ(B) + q : q ∈ P, q > B}`. -/
def markJ1 (P : ℕ) (Bs : List ℕ) : ℕ :=
  Bs.foldr (fun B acc => acc ||| shiftAbove P B (dsum B B)) 0

theorem markJ1_sound (P N : ℕ) :
    ∀ Bs : List ℕ, (markJ1 P Bs).testBit N = true →
      ∃ B ∈ Bs, B + 1 + dsum B B ≤ N ∧ P.testBit (N - dsum B B) = true
  | [], h => by simp [markJ1] at h
  | B :: Bs, h => by
    have h' : ((markJ1 P Bs) ||| shiftAbove P B (dsum B B)).testBit N = true := h
    rw [Nat.testBit_or, Bool.or_eq_true] at h'
    rcases h' with h1 | h1
    · obtain ⟨B', hB', h2⟩ := markJ1_sound P N Bs h1
      exact ⟨B', List.mem_cons_of_mem B hB', h2⟩
    · exact ⟨B, List.mem_cons_self, testBit_shiftAbove h1⟩

/-- The integer a witness `(B, d, q)` stands for: `σ(B) + q · Fdiv B d`. -/
def wval (w : ℕ × ℕ × ℕ) : ℕ := dsum w.1 w.1 + w.2.2 * dsum w.1 w.2.1

/-- The test of a witness `(B, d, q)` against the prime bitset `P`:
`1 ≤ B ≤ 1000`, `B < q`, `d ∣ B`, bit `q` of `P`. -/
def okW (P : ℕ) (w : ℕ × ℕ × ℕ) : Bool :=
  Nat.ble 1 w.1 && Nat.ble w.1 1000 && Nat.blt w.1 w.2.2 && w.1 % w.2.1 == 0 &&
    P.testBit w.2.2

/-- The witnessed marks: bit `wval w` for every `w ∈ Ws`. -/
def markW (Ws : List (ℕ × ℕ × ℕ)) : ℕ :=
  Ws.foldr (fun w acc => acc ||| (1 <<< wval w)) 0

theorem markW_sound (N : ℕ) :
    ∀ Ws : List (ℕ × ℕ × ℕ), (markW Ws).testBit N = true → ∃ w ∈ Ws, N = wval w
  | [], h => by simp [markW] at h
  | w :: Ws, h => by
    have h' : ((markW Ws) ||| (1 <<< wval w)).testBit N = true := h
    rw [Nat.testBit_or, Bool.or_eq_true] at h'
    rcases h' with h1 | h1
    · obtain ⟨w', hw', h2⟩ := markW_sound N Ws h1
      exact ⟨w', List.mem_cons_of_mem w hw', h2⟩
    · refine ⟨w, List.mem_cons_self, ?_⟩
      rw [Nat.one_shiftLeft, Nat.testBit_two_pow] at h1
      exact (of_decide_eq_true h1).symm

/-- **The small-window check**: every bit of `[lo, hi]` is set in
`markJ1 P Bs ||| markW Ws ||| 2^7`, every `B ∈ Bs` is in `[1, 1000]`, and every witness passes
`okW`. -/
def smallChk (P : ℕ) (Bs : List ℕ) (Ws : List (ℕ × ℕ × ℕ)) (lo hi : ℕ) : Bool :=
  allOnes (markJ1 P Bs ||| markW Ws ||| (1 <<< 7)) lo hi &&
    Bs.all (fun B => Nat.ble 1 B && Nat.ble B 1000) && Ws.all (okW P)

/-- **Soundness of the small-window check.** If `smallChk (primeBits L) Bs Ws lo hi` holds, then
every `N ∈ [lo, hi]` other than `7` is marked (`smallSieveMarked`, the existential of
`Comp_Verifier_small`). -/
theorem marked_of_smallChk {L lo hi : ℕ} {Bs : List ℕ} {Ws : List (ℕ × ℕ × ℕ)}
    (h : smallChk (primeBits L) Bs Ws lo hi = true) :
    ∀ N : ℕ, lo ≤ N → N ≤ hi → N ≠ 7 → smallSieveMarked N := by
  intro N hlo hhi h7
  unfold smallChk at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨hall, hBs⟩, hWs⟩ := h
  have hbit := allOnes_sound hall hlo hhi
  rw [Nat.testBit_or, Nat.testBit_or, Bool.or_eq_true, Bool.or_eq_true] at hbit
  rcases hbit with (h1 | h1) | h1
  · obtain ⟨B, hB, hle, hP⟩ := markJ1_sound _ N Bs h1
    have hBr := hBs B hB
    simp only [Nat.ble_eq] at hBr
    obtain ⟨hB1, hB2⟩ := hBr
    obtain ⟨-, hq⟩ := (testBit_primeBits L _).1 hP
    have hmk := marked_of_Fdiv hB1 hB2 hq (by omega) (one_dvd B)
    rw [← dsum_eq_Fdiv B hB1, dsum_one, sig_eq_dsum B hB1, Nat.mul_one] at hmk
    have he : dsum B B + (N - dsum B B) = N := by omega
    rwa [he] at hmk
  · obtain ⟨⟨B, d, q⟩, hw, rfl⟩ := markW_sound N Ws h1
    have hok := hWs _ hw
    simp only [okW, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq, beq_iff_eq] at hok
    obtain ⟨⟨⟨⟨hB1, hB2⟩, hlt⟩, hd⟩, hP⟩ := hok
    obtain ⟨-, hq⟩ := (testBit_primeBits L q).1 hP
    have hmk := marked_of_Fdiv hB1 hB2 hq hlt (Nat.dvd_of_mod_eq_zero hd)
    rw [← dsum_eq_Fdiv B hB1, sig_eq_dsum B hB1] at hmk
    exact hmk
  · rw [Nat.one_shiftLeft, Nat.testBit_two_pow] at h1
    exact absurd (of_decide_eq_true h1).symm h7

end Principia.Erdos1054.Alt7.Small
