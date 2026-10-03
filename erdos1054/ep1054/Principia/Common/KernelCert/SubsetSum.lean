/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.KernelCert.Bits
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Data.Finset.Card

set_option autoImplicit false

/-!
# Kernel certificates: subset sums by a bitset dynamic programme

## The programme

`ssBitsW f l bound` is the set of all `∑_{p ∈ S} f p` (`S` a sub-list of `l`) that are `≤ bound`,
as a bitset: starting from `{0}`, each element `p` maps `X ↦ (X ∪ (X + f p)) ∩ [0, bound]`, i.e.
`(X ||| (X <<< f p)) &&& lowMask (bound + 1)`. `ssBits l bound = ssBitsW id l bound`.

* `ssBitsW_sound`: for a duplicate-free `l`, a set bit `n` is `≤ bound` and is `∑_{p ∈ S} f p`
  for some `S ⊆ l.toFinset`. With `f = id` this is membership in `{N | ∃ S ⊆ P, ∑ p ∈ S, p = N}`
  (`Principia.Erdos1054.subsetSums`), with `P = l.toFinset`.
* The weight `f` lets a narrow band of large numbers be handled in a narrow bitset: for primes in
  a band `[a, a + δ)` take `f p = (p − d)/2`; `ksum_cover` recovers `∑ p = 2n + k d` for the
  `k`-element subsets, the cardinality being pinned by the weight bounds (`card_pin`).
* `Cov2 P k a b` ("every `N ∈ [a, b]` of the parity of `a` is a sum of `k` distinct elements of
  `P`") is closed under adjoining a list whose consecutive gaps are `≤ b − a` (`Cov2.extend`) —
  the interval-extension argument, one level up, with no bitset at all.

## Kernel cost (measured, v4.31.0)

Every intermediate bitset is retained by the kernel until the declaration is checked (see
`Bits.lean`), so the memory of one `decide +kernel` over `ssBitsW` is about three bitsets per list
element: 1800 steps on a 9·10^4-bit bitset cost well under 0.1 GB, while on a `1.56·10^8`-bit
bitset 10, 30 and 60 steps peaked at 0.70, 1.82 and 3.58 GB (3.4, 4.8, 9.1 s) — linear, ~58 MB
per step, so the 1164-prime programme would need ~68 GB.

`ssRun` tests `acc == 0` before each step: the test forces the kernel to evaluate the accumulator
in order, so the lazy accumulator never becomes a term nested as deep as the list (a correct `0`
result is harmless — it has no set bits).
-/

namespace Principia.Common.KernelCert

open Finset

/-- One step of the programme: `(acc ∪ (acc + w)) ∩ mask`. -/
def ssStep (m w acc : ℕ) : ℕ := (acc ||| (acc <<< w)) &&& m

/-- Run the programme over a list, element `p` shifting by `f p`. -/
def ssRun (f : ℕ → ℕ) (m : ℕ) : List ℕ → ℕ → ℕ
  | [], acc => acc
  | p :: l, acc => if acc == 0 then 0 else ssRun f m l (ssStep m (f p) acc)

/-- **The weighted subset sums of `l` that are `≤ bound`**, as a bitset. -/
def ssBitsW (f : ℕ → ℕ) (l : List ℕ) (bound : ℕ) : ℕ := ssRun f (lowMask (bound + 1)) l 1

/-- **The subset sums of `l` that are `≤ bound`**, as a bitset. -/
def ssBits (l : List ℕ) (bound : ℕ) : ℕ := ssBitsW id l bound

theorem testBit_ssStep (m w acc n : ℕ) :
    (ssStep m w acc).testBit n =
      ((acc.testBit n || (decide (n ≥ w) && acc.testBit (n - w))) && m.testBit n) := by
  simp [ssStep, Nat.testBit_and, Nat.testBit_or, Nat.testBit_shiftLeft]

/-- Every set bit of the result is a set bit of the mask, if every bit of the start is. -/
theorem ssRun_mask (f : ℕ → ℕ) (m : ℕ) :
    ∀ (l : List ℕ) (acc : ℕ), (∀ n, acc.testBit n = true → m.testBit n = true) →
      ∀ n, (ssRun f m l acc).testBit n = true → m.testBit n = true
  | [], acc, h => fun n hn => h n hn
  | p :: l, acc, h => by
      intro n hn
      simp only [ssRun] at hn
      split_ifs at hn with h0
      · simp at hn
      · refine ssRun_mask f m l _ (fun k hk => ?_) n hn
        rw [testBit_ssStep] at hk
        simp only [Bool.and_eq_true] at hk
        exact hk.2

/-- The invariant of the programme: every set bit is a weighted subset sum of `D`. -/
theorem ssRun_sound (f : ℕ → ℕ) (m : ℕ) :
    ∀ (l : List ℕ) (acc : ℕ) (D : Finset ℕ), l.Nodup → (∀ p ∈ l, p ∉ D) →
      (∀ n, acc.testBit n = true → ∃ S ⊆ D, ∑ p ∈ S, f p = n) →
      ∀ n, (ssRun f m l acc).testBit n = true → ∃ S ⊆ D ∪ l.toFinset, ∑ p ∈ S, f p = n
  | [], acc, D, _, _, h => by
      intro n hn
      obtain ⟨S, hS, hsum⟩ := h n hn
      exact ⟨S, fun x hx => Finset.mem_union_left _ (hS hx), hsum⟩
  | p :: l, acc, D, hnd, hdisj, h => by
      intro n hn
      simp only [ssRun] at hn
      split_ifs at hn with h0
      · simp at hn
      · have hnd' := List.nodup_cons.1 hnd
        have hpD : p ∉ D := hdisj p (by simp)
        have key := ssRun_sound f m l (ssStep m (f p) acc) (insert p D) hnd'.2
          (by
            intro q hq
            rw [Finset.mem_insert]
            rintro (rfl | hqD)
            · exact hnd'.1 hq
            · exact hdisj q (by simp [hq]) hqD)
          (by
            intro k hk
            rw [testBit_ssStep] at hk
            simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hk
            rcases hk.1 with hk1 | ⟨hk2, hk3⟩
            · obtain ⟨S, hS, hsum⟩ := h k hk1
              exact ⟨S, fun x hx => Finset.mem_insert_of_mem (hS hx), hsum⟩
            · obtain ⟨S, hS, hsum⟩ := h (k - f p) hk3
              have hpS : p ∉ S := fun hp => hpD (hS hp)
              refine ⟨insert p S, Finset.insert_subset_insert p hS, ?_⟩
              rw [Finset.sum_insert hpS, hsum]
              omega)
          n hn
        obtain ⟨S, hS, hsum⟩ := key
        refine ⟨S, fun x hx => ?_, hsum⟩
        have := hS hx
        simp only [Finset.mem_union, Finset.mem_insert, List.mem_toFinset,
          List.mem_cons] at this ⊢
        tauto

/-- **Soundness of the weighted subset-sum bitset.** For a duplicate-free list, a set bit `n` is
`≤ bound` and is `∑_{p ∈ S} f p` for some `S ⊆ l.toFinset`. -/
theorem ssBitsW_sound (f : ℕ → ℕ) {l : List ℕ} (hl : l.Nodup) {bound n : ℕ}
    (h : (ssBitsW f l bound).testBit n = true) :
    n ≤ bound ∧ ∃ S ⊆ l.toFinset, ∑ p ∈ S, f p = n := by
  have h1 : ∀ k, (1 : ℕ).testBit k = true → k = 0 := fun k hk =>
    Nat.testBit_one_eq_true_iff_self_eq_zero.1 hk
  refine ⟨?_, ?_⟩
  · have := ssRun_mask f (lowMask (bound + 1)) l 1 (fun k hk => by
      rw [h1 k hk, testBit_lowMask]
      simp) n h
    rw [testBit_lowMask] at this
    simp at this
    omega
  · obtain ⟨S, hS, hsum⟩ := ssRun_sound f (lowMask (bound + 1)) l 1 ∅ hl (by simp)
      (fun k hk => ⟨∅, Finset.empty_subset _, by rw [h1 k hk]; simp⟩) n h
    exact ⟨S, by simpa using hS, hsum⟩

/-- **Soundness of the subset-sum bitset**, in the shape of `{N | ∃ S ⊆ P, ∑ p ∈ S, p = N}` with
`P = l.toFinset`. -/
theorem ssBits_sound {l : List ℕ} (hl : l.Nodup) {bound n : ℕ}
    (h : (ssBits l bound).testBit n = true) :
    n ≤ bound ∧ ∃ S ⊆ l.toFinset, ∑ p ∈ S, p = n :=
  ssBitsW_sound id hl h

/-- **Interval cover from one kernel check**: if every bit of `[a, b]` of `ssBits l bound` is
set, every `N ∈ [a, b]` is a sum of distinct elements of `l`. -/
theorem ssBits_cover {l : List ℕ} (hl : l.Nodup) {bound a b : ℕ}
    (h : allOnes (ssBits l bound) a b = true) :
    ∀ N, a ≤ N → N ≤ b → ∃ S ⊆ l.toFinset, ∑ p ∈ S, p = N :=
  fun _ ha hb => (ssBits_sound hl (allOnes_sound h ha hb)).2

/-- **Cardinality from weight bounds.** If every weight lies in `[lo, hi]` and the total `n`
satisfies `(k − 1)·hi < n < (k + 1)·lo`, then exactly `k` elements were used. -/
theorem card_pin {S : Finset ℕ} {w : ℕ → ℕ} {lo hi k n : ℕ}
    (hw : ∀ p ∈ S, lo ≤ w p ∧ w p ≤ hi) (hs : ∑ p ∈ S, w p = n)
    (h0 : (k - 1) * hi < n) (h1 : n < (k + 1) * lo) : S.card = k := by
  have hlo : S.card * lo ≤ n := by
    rw [← hs, ← smul_eq_mul]
    exact Finset.card_nsmul_le_sum S w lo (fun p hp => (hw p hp).1)
  have hhi : n ≤ S.card * hi := by
    rw [← hs, ← smul_eq_mul]
    exact Finset.sum_le_card_nsmul S w hi (fun p hp => (hw p hp).2)
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · have : S.card * hi ≤ (k - 1) * hi := Nat.mul_le_mul_right hi (by omega)
    omega
  · have : (k + 1) * lo ≤ S.card * lo := Nat.mul_le_mul_right lo hgt
    omega

/-- **`k`-element sums from a half-offset programme.** For a duplicate-free list `F` whose
elements satisfy `p ≥ d`, `p ≡ d (mod 2)` and `(p − d)/2 ∈ [lo, hi]`, if the programme with
weights `(p − d)/2` has every bit of `[n0, n1]` set and `(k − 1)·hi < n0`, `n1 < (k + 1)·lo`,
then every `2n + k d` with `n ∈ [n0, n1]` is the sum of a `k`-element subset of `F`. -/
theorem ksum_cover {F : List ℕ} (hF : F.Nodup) {d lo hi k n0 n1 bound : ℕ}
    (hmem : ∀ p ∈ F, d ≤ p ∧ (p - d) % 2 = 0 ∧ lo ≤ (p - d) / 2 ∧ (p - d) / 2 ≤ hi)
    (h0 : (k - 1) * hi < n0) (h1 : n1 < (k + 1) * lo)
    (hall : allOnes (ssBitsW (fun p => (p - d) / 2) F bound) n0 n1 = true) :
    ∀ n, n0 ≤ n → n ≤ n1 → ∃ S ⊆ F.toFinset, S.card = k ∧ ∑ p ∈ S, p = 2 * n + k * d := by
  intro n hn0 hn1
  obtain ⟨-, S, hS, hsum⟩ := ssBitsW_sound (fun p => (p - d) / 2) hF (allOnes_sound hall hn0 hn1)
  have hSF : ∀ p ∈ S, d ≤ p ∧ (p - d) % 2 = 0 ∧ lo ≤ (p - d) / 2 ∧ (p - d) / 2 ≤ hi :=
    fun p hp => hmem p (by simpa using hS hp)
  have hcard : S.card = k :=
    card_pin (w := fun p => (p - d) / 2) (fun p hp => ⟨(hSF p hp).2.2.1, (hSF p hp).2.2.2⟩)
      hsum (by omega) (by omega)
  refine ⟨S, hS, hcard, ?_⟩
  have hp : ∀ p ∈ S, p = 2 * ((p - d) / 2) + d := fun p hp => by
    have := hSF p hp
    omega
  rw [Finset.sum_congr rfl hp, Finset.sum_add_distrib, ← Finset.mul_sum, hsum,
    Finset.sum_const, hcard, smul_eq_mul]

/-- `Cov2 P k a b`: every `N ∈ [a, b]` with `N ≡ a (mod 2)` is the sum of a `k`-element subset
of `P`. -/
def Cov2 (P : Finset ℕ) (k a b : ℕ) : Prop :=
  ∀ N, a ≤ N → N ≤ b → N % 2 = a % 2 → ∃ S ⊆ P, S.card = k ∧ ∑ p ∈ S, p = N

/-- `ksum_cover` in `Cov2` form: the `k`-sums cover `[2n0 + kd, 2n1 + kd]` in steps of `2`. -/
theorem cov2_of_ksum {F : List ℕ} {d k n0 n1 : ℕ}
    (h : ∀ n, n0 ≤ n → n ≤ n1 → ∃ S ⊆ F.toFinset, S.card = k ∧ ∑ p ∈ S, p = 2 * n + k * d) :
    Cov2 F.toFinset k (2 * n0 + k * d) (2 * n1 + k * d) := by
  intro N hN0 hN1 hpar
  obtain ⟨S, hS, hc, hs⟩ := h ((N - k * d) / 2) (by omega) (by omega)
  exact ⟨S, hS, hc, by rw [hs]; omega⟩

/-- `chainTo g hi l`: `l` is strictly increasing, consecutive gaps are `≤ g`, and its last
element is `hi` (`false` on the empty list). -/
def chainTo (g hi : ℕ) : List ℕ → Bool
  | [] => false
  | [x] => x == hi
  | x :: y :: l => decide (x < y) && decide (y ≤ x + g) && chainTo g hi (y :: l)

theorem chainTo_le {g hi : ℕ} :
    ∀ (x : ℕ) (l : List ℕ), chainTo g hi (x :: l) = true → ∀ y ∈ x :: l, x ≤ y
  | x, [], _ => by simp
  | x, y :: l, h => by
      simp only [chainTo, Bool.and_eq_true, decide_eq_true_eq] at h
      intro z hz
      rcases List.mem_cons.1 hz with rfl | hz
      · exact le_rfl
      · exact (h.1.1.le).trans (chainTo_le y l h.2 z hz)

theorem chainTo_nodup {g hi : ℕ} : ∀ l : List ℕ, chainTo g hi l = true → l.Nodup
  | [], _ => List.nodup_nil
  | [x], _ => List.nodup_singleton x
  | x :: y :: l, h => by
      have h' := h
      simp only [chainTo, Bool.and_eq_true, decide_eq_true_eq] at h'
      refine List.nodup_cons.2 ⟨fun hx => ?_, chainTo_nodup (y :: l) h'.2⟩
      have := chainTo_le y l h'.2 x hx
      omega

/-- The first element of a `chainTo` list is its minimum; the last is `hi`. -/
theorem chainTo_mem_le {g hi : ℕ} :
    ∀ (x : ℕ) (l : List ℕ), chainTo g hi (x :: l) = true → ∀ y ∈ x :: l, y ≤ hi
  | x, [], h => by
      simp only [chainTo, beq_iff_eq] at h
      simp [h]
  | x, y :: l, h => by
      simp only [chainTo, Bool.and_eq_true, decide_eq_true_eq] at h
      intro z hz
      rcases List.mem_cons.1 hz with rfl | hz
      · exact h.1.1.le.trans (chainTo_mem_le y l h.2 y (by simp))
      · exact chainTo_mem_le y l h.2 z hz

/-- **Gap hitting.** In a `chainTo g hi (x :: l)` list, every `t ∈ [x, hi + g]` has an element
`y ≤ t ≤ y + g`. -/
theorem chainTo_hit {g hi : ℕ} :
    ∀ (x : ℕ) (l : List ℕ), chainTo g hi (x :: l) = true →
      ∀ t, x ≤ t → t ≤ hi + g → ∃ y ∈ x :: l, y ≤ t ∧ t ≤ y + g
  | x, [], h => by
      simp only [chainTo, beq_iff_eq] at h
      intro t hxt hth
      exact ⟨x, by simp, hxt, by omega⟩
  | x, y :: l, h => by
      simp only [chainTo, Bool.and_eq_true, decide_eq_true_eq] at h
      intro t hxt hth
      by_cases hty : t < y
      · exact ⟨x, by simp, hxt, by omega⟩
      · obtain ⟨z, hz, h1, h2⟩ := chainTo_hit y l h.2 t (by omega) hth
        exact ⟨z, List.mem_cons_of_mem x hz, h1, h2⟩

/-- **Interval extension by a gap list.** If `Cov2 P k a b` and `lo :: Q` is a `chainTo (b − a)
hi` list of elements of one parity, none in `P`, then `Cov2 (P ∪ (lo :: Q)) (k + 1) (a + lo)
(b + hi)`: every such `N` is `M + y` with `M ∈ [a, b]` covered and `y` a new element. -/
theorem Cov2.extend {P : Finset ℕ} {k a b : ℕ} (h : Cov2 P k a b) (hab : a ≤ b) {lo hi : ℕ}
    {Q : List ℕ} (hchain : chainTo (b - a) hi (lo :: Q) = true)
    (hpar : ∀ y ∈ lo :: Q, y % 2 = lo % 2) (hdisj : ∀ y ∈ lo :: Q, y ∉ P) :
    Cov2 (P ∪ (lo :: Q).toFinset) (k + 1) (a + lo) (b + hi) := by
  intro N hN0 hN1 hpar'
  obtain ⟨y, hy, hy1, hy2⟩ := chainTo_hit lo Q hchain (N - a) (by omega) (by omega)
  have hyp := hpar y hy
  obtain ⟨S, hS, hc, hs⟩ := h (N - y) (by omega) (by omega) (by omega)
  have hyS : y ∉ S := fun hmem => hdisj y hy (hS hmem)
  refine ⟨insert y S, ?_, ?_, ?_⟩
  · intro z hz
    rcases Finset.mem_insert.1 hz with rfl | hz
    · exact Finset.mem_union_right _ (List.mem_toFinset.2 hy)
    · exact Finset.mem_union_left _ (hS hz)
  · rw [Finset.card_insert_of_notMem hyS, hc]
  · rw [Finset.sum_insert hyS, hs]
    omega

/-- `Cov2.extend` for a list given by its first element: `l.head? = some lo`. -/
theorem Cov2.extend_list {P : Finset ℕ} {k a b : ℕ} (h : Cov2 P k a b) (hab : a ≤ b)
    {lo hi : ℕ} {l : List ℕ} (hhead : l.head? = some lo) (hchain : chainTo (b - a) hi l = true)
    (hpar : ∀ y ∈ l, y % 2 = lo % 2) (hdisj : ∀ y ∈ l, y ∉ P) :
    Cov2 (P ∪ l.toFinset) (k + 1) (a + lo) (b + hi) := by
  rcases l with _ | ⟨x, Q⟩
  · simp at hhead
  · simp only [List.head?_cons, Option.some.injEq] at hhead
    subst hhead
    exact h.extend hab hchain hpar hdisj

/-- Enlarging the ambient set keeps a cover. -/
theorem Cov2.mono {P P' : Finset ℕ} {k a b : ℕ} (h : Cov2 P k a b) (hPP : P ⊆ P') :
    Cov2 P' k a b := by
  intro N h0 h1 h2
  obtain ⟨S, hS, hc, hs⟩ := h N h0 h1 h2
  exact ⟨S, hS.trans hPP, hc, hs⟩

end Principia.Common.KernelCert
