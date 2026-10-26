import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.NormNum.NatFactorial
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.Push


set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-!
# MathDB #345259 — a nonunimodal line in a four-colour partition array

Write-up: `mathdb-open-problems/problems/345259/solution.tex` on the collaborator branch
`mathdb-results` of `antoshashakov/Principia-Math-In-Progress`.

The conjecture asserts that a certain line of a four-colour partition array is unimodal.
It is refuted by three adjacent coefficients that go DOWN then UP:
`(11,1,1) ↦ 95004`, `(10,2,2) ↦ 90090`, `(9,3,3) ↦ 100100`.  All three are confirmed by
full enumeration in `Campaigns/MathDB-Formalization/verify_345259.py`.

Partitions are encoded by multiplicity vector `m : Fin 15 → ℕ`, `m i` counting parts equal
to `i + 1`.  The box holds 2,415,043 partitions, far too many to enumerate in the kernel,
but only **505** have at least 13 distinct part sizes and the three coefficients depend on
nothing else: `f_13 = 504` (`Fam13_card`), `f_14 = 0` (`card14`), `f_15 = 1` (`card15`).

**The counterexample is complete.**  `main` shows the three adjacent coefficients go DOWN
then UP, so the line is not unimodal.  Getting `Coeff 11 1 1` there took two habits that are
recorded at the point of use: keep `PartsF` behind an opaque `def` so its `16^15`-element
`piFinset` is never `whnf`'d, and instantiate manipulation lemmas as ASCRIBED TERMS rather
than rewriting with them.  Both were found by measurement — the natural phrasings cost
7.6–11 GB and were killed by the OS.
-/

namespace Principia.MathDB.P345259

open Finset

/-! ### Partitions of 120 in the 15 x 15 box, by multiplicity vector -/

/-- `m i` is the number of parts equal to `i + 1`. -/
def Wt (m : Fin 15 → ℕ) : ℕ := ∑ i, (i.val + 1) * m i

def Len (m : Fin 15 → ℕ) : ℕ := ∑ i, m i

def Supp (m : Fin 15 → ℕ) : Finset (Fin 15) := univ.filter (fun i => m i ≠ 0)

/-- A partition of `120` with at most `15` parts, each at most `15`. -/
def IsPart (m : Fin 15 → ℕ) : Prop := Wt m = 120 ∧ Len m ≤ 15

theorem mem_Supp {m : Fin 15 → ℕ} {i : Fin 15} : i ∈ Supp m ↔ m i ≠ 0 := by
  simp [Supp]

theorem one_le_of_mem_Supp {m : Fin 15 → ℕ} {i : Fin 15} (h : i ∈ Supp m) : 1 ≤ m i :=
  Nat.one_le_iff_ne_zero.mpr (mem_Supp.mp h)

theorem Len_eq (m : Fin 15 → ℕ) : Len m = ∑ i ∈ Supp m, m i := by
  rw [Len, ← Finset.sum_filter_ne_zero univ]
  rfl

theorem Wt_eq (m : Fin 15 → ℕ) : Wt m = ∑ i ∈ Supp m, (i.val + 1) * m i := by
  rw [Wt]
  refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
  intro i _ hi
  rw [mem_Supp, not_not] at hi
  simp [hi]

/-- The excess: how many parts beyond one of each distinct size. -/
def Exc (m : Fin 15 → ℕ) : ℕ := ∑ i ∈ Supp m, (m i - 1)

/-- and the weight that excess carries. -/
def ExcWt (m : Fin 15 → ℕ) : ℕ := ∑ i ∈ Supp m, (i.val + 1) * (m i - 1)

theorem Len_split (m : Fin 15 → ℕ) : Len m = (Supp m).card + Exc m := by
  rw [Len_eq, Exc, Finset.card_eq_sum_ones, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i hi => ?_
  have := one_le_of_mem_Supp hi
  omega

theorem Wt_split (m : Fin 15 → ℕ) :
    Wt m = (∑ i ∈ Supp m, (i.val + 1)) + ExcWt m := by
  rw [Wt_eq, ExcWt, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i hi => ?_
  have h1 := one_le_of_mem_Supp hi
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h1
  rw [hk]
  simp only [Nat.add_sub_cancel_left]
  ring

theorem sum_univ_sizes : ∑ i : Fin 15, (i.val + 1) = 120 := by decide

theorem supp_sum_eq (m : Fin 15 → ℕ) :
    (∑ i ∈ Supp m, (i.val + 1)) + (∑ i ∈ (Supp m)ᶜ, (i.val + 1)) = 120 := by
  rw [Finset.sum_add_sum_compl, sum_univ_sizes]

theorem card_supp_le_len (m : Fin 15 → ℕ) : (Supp m).card ≤ Len m := by
  rw [Len_split]
  omega

/-! ### The three counts at the top of the array -/

/-- **`f_15 = 1`**: the only partition with all fifteen sizes is `1 + 2 + ... + 15`. -/
theorem card15 (m : Fin 15 → ℕ) (h : IsPart m) (hc : (Supp m).card = 15) :
    m = fun _ => 1 := by
  obtain ⟨hw, hl⟩ := h
  have hlen : Len m = 15 := le_antisymm hl (by rw [Len_split, hc]; omega)
  have hexc : Exc m = 0 := by rw [Len_split, hc] at hlen; omega
  have huniv : Supp m = univ := Finset.eq_univ_of_card _ (by rw [hc]; rfl)
  funext i
  have hi : i ∈ Supp m := by rw [huniv]; exact mem_univ i
  have h1 := one_le_of_mem_Supp hi
  have : m i - 1 = 0 := by
    have := Finset.sum_eq_zero_iff.mp hexc i hi
    exact this
  omega

/-- **`f_14 = 0`**: no partition has exactly fourteen distinct sizes. -/
theorem card14 (m : Fin 15 → ℕ) (h : IsPart m) (hc : (Supp m).card = 14) : False := by
  obtain ⟨hw, hl⟩ := h
  -- the single missing size
  have hcompl : ((Supp m)ᶜ).card = 1 := by
    have := Finset.card_compl (Supp m)
    simp only [Fintype.card_fin] at this
    omega
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcompl
  have hsum : (∑ i ∈ (Supp m)ᶜ, (i.val + 1)) = a.val + 1 := by
    rw [ha, Finset.sum_singleton]
  have hbase : (∑ i ∈ Supp m, (i.val + 1)) = 120 - (a.val + 1) := by
    have := supp_sum_eq m
    omega
  have halt : a.val < 15 := a.isLt
  have hexcwt : ExcWt m = a.val + 1 := by
    rw [Wt_split, hbase] at hw
    omega
  have hexc : Exc m ≤ 1 := by
    rw [Len_split, hc] at hl
    omega
  -- the excess carries weight `a+1`, so it is a single part of size `a+1`, i.e. index `a`
  have hane : a ∉ Supp m := by
    have : a ∈ (Supp m)ᶜ := by rw [ha]; exact Finset.mem_singleton_self a
    simpa using this
  rcases Nat.eq_zero_or_pos (Exc m) with h0 | h1
  · have : ExcWt m = 0 := by
      rw [ExcWt]
      refine Finset.sum_eq_zero fun i hi => ?_
      have := Finset.sum_eq_zero_iff.mp h0 i hi
      simp [this]
    omega
  · -- exactly one excess part
    have hone : Exc m = 1 := by omega
    obtain ⟨c, hcS, hc1⟩ : ∃ c ∈ Supp m, m c - 1 = 1 := by
      by_contra hcon
      push_neg at hcon
      have : Exc m = 0 := by
        refine Finset.sum_eq_zero fun i hi => ?_
        have hle : m i - 1 ≤ Exc m := Finset.single_le_sum
          (f := fun j => m j - 1) (fun _ _ => Nat.zero_le _) hi
        have := hcon i hi
        omega
      omega
    have hsplit : (m c - 1) + ∑ j ∈ (Supp m).erase c, (m j - 1) = Exc m :=
      Finset.add_sum_erase _ (fun j => m j - 1) hcS
    have hrest : ∀ i ∈ Supp m, i ≠ c → m i - 1 = 0 := by
      intro i hi hne
      have hmem : i ∈ (Supp m).erase c := Finset.mem_erase.mpr ⟨hne, hi⟩
      have hle : m i - 1 ≤ ∑ j ∈ (Supp m).erase c, (m j - 1) :=
        Finset.single_le_sum (f := fun j => m j - 1) (fun _ _ => Nat.zero_le _) hmem
      omega
    have hzero : ∑ i ∈ (Supp m).erase c, (i.val + 1) * (m i - 1) = 0 := by
      refine Finset.sum_eq_zero fun i hi => ?_
      obtain ⟨hne, hiS⟩ := Finset.mem_erase.mp hi
      rw [hrest i hiS hne, mul_zero]
    have hwc : ExcWt m = c.val + 1 := by
      have hsp : (c.val + 1) * (m c - 1)
          + ∑ i ∈ (Supp m).erase c, (i.val + 1) * (m i - 1) = ExcWt m :=
        Finset.add_sum_erase _ (fun j => (j.val + 1) * (m j - 1)) hcS
      rw [hc1, mul_one, hzero] at hsp
      omega
    have hca : c = a := Fin.val_injective (by omega)
    exact hane (hca ▸ hcS)

/-! ### The two shapes a 13-distinct-size partition can take -/

/-- One extra part: sizes `a+1` and `b+1` missing, one doubled part at index `c`. -/
def mk1 (a b c : Fin 15) : Fin 15 → ℕ :=
  fun i => (if i = a ∨ i = b then 0 else 1) + (if i = c then 1 else 0)

/-- Two extra parts, at indices `c ≤ d` (equal when a single part is tripled). -/
def mk2 (a b c d : Fin 15) : Fin 15 → ℕ :=
  fun i => (if i = a ∨ i = b then 0 else 1) + (if i = c then 1 else 0)
    + (if i = d then 1 else 0)

/-- Parameters for the one-extra shape: the extra part has size `(a+1)+(b+1)`. -/
def P1 : Finset (Fin 15 × Fin 15 × Fin 15) :=
  univ.filter (fun p => p.1.val < p.2.1.val ∧ p.2.2.val = p.1.val + p.2.1.val + 1)

/-- Parameters for the two-extra shape. -/
def P2 : Finset (Fin 15 × Fin 15 × Fin 15 × Fin 15) :=
  univ.filter (fun q => q.1.val < q.2.1.val ∧ q.2.2.1.val ≤ q.2.2.2.val ∧
    q.2.2.1.val + q.2.2.2.val = q.1.val + q.2.1.val ∧
    q.2.2.1 ≠ q.1 ∧ q.2.2.1 ≠ q.2.1 ∧ q.2.2.2 ≠ q.1 ∧ q.2.2.2 ≠ q.2.1)

theorem P1_card : P1.card = 49 := by decide

theorem P2_card : P2.card = 455 := by decide

theorem mem_P1 {p : Fin 15 × Fin 15 × Fin 15} (hp : p ∈ P1) :
    p.1.val < p.2.1.val ∧ p.2.2.val = p.1.val + p.2.1.val + 1 := by
  simpa [P1] using hp

theorem mem_P2 {q : Fin 15 × Fin 15 × Fin 15 × Fin 15} (hq : q ∈ P2) :
    q.1.val < q.2.1.val ∧ q.2.2.1.val ≤ q.2.2.2.val ∧
      q.2.2.1.val + q.2.2.2.val = q.1.val + q.2.1.val ∧
      q.2.2.1 ≠ q.1 ∧ q.2.2.1 ≠ q.2.1 ∧ q.2.2.2 ≠ q.1 ∧ q.2.2.2 ≠ q.2.1 := by
  simpa [P2] using hq

/-! ### Reading the parameters back off the vector -/

theorem mk1_zeros (a b c : Fin 15) (hca : c ≠ a) (hcb : c ≠ b) (i : Fin 15) :
    mk1 a b c i = 0 ↔ (i = a ∨ i = b) := by
  unfold mk1
  by_cases h : i = a ∨ i = b
  · have hic : i ≠ c := by
      rcases h with rfl | rfl
      · exact fun hh => hca hh.symm
      · exact fun hh => hcb hh.symm
    simp [h, hic]
  · simp [h]

theorem mk2_zeros (a b c d : Fin 15) (hca : c ≠ a) (hcb : c ≠ b) (hda : d ≠ a)
    (hdb : d ≠ b) (i : Fin 15) : mk2 a b c d i = 0 ↔ (i = a ∨ i = b) := by
  unfold mk2
  by_cases h : i = a ∨ i = b
  · have hic : i ≠ c := by
      rcases h with rfl | rfl
      · exact fun hh => hca hh.symm
      · exact fun hh => hcb hh.symm
    have hid : i ≠ d := by
      rcases h with rfl | rfl
      · exact fun hh => hda hh.symm
      · exact fun hh => hdb hh.symm
    simp [h, hic, hid]
  · simp [h]

/-- Summing a function over everything except two points. -/
theorem sum_except_two (f : Fin 15 → ℕ) (a b : Fin 15) (hab : a ≠ b) :
    (∑ i, (if i = a ∨ i = b then 0 else f i)) + (f a + f b) = ∑ i, f i := by
  have hpair : ∑ x ∈ ({a, b} : Finset (Fin 15)), f x = f a + f b := Finset.sum_pair hab
  have hsd := Finset.sum_sdiff (f := f) (Finset.subset_univ ({a, b} : Finset (Fin 15)))
  have hfil : ∑ i : Fin 15, (if i = a ∨ i = b then 0 else f i)
      = ∑ i ∈ univ \ ({a, b} : Finset (Fin 15)), f i := by
    rw [Finset.sdiff_eq_filter, Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : i = a ∨ i = b <;> simp [h]
  rw [hfil]
  omega

theorem sum_one : ∑ _i : Fin 15, (1 : ℕ) = 15 := by decide

theorem sum_sizes : ∑ i : Fin 15, (i.val + 1) = 120 := by decide

/-! ### Length and weight of the two shapes -/

theorem mk1_len (a b c : Fin 15) (hab : a ≠ b) : ∑ i, mk1 a b c i = 14 := by
  unfold mk1
  rw [Finset.sum_add_distrib]
  have h1 := sum_except_two (fun _ => 1) a b hab
  rw [sum_one] at h1
  have h2 : ∑ i : Fin 15, (if i = c then (1 : ℕ) else 0) = 1 := by simp
  omega

theorem mk1_wt (a b c : Fin 15) (hab : a ≠ b) :
    (∑ i, (i.val + 1) * mk1 a b c i) + ((a.val + 1) + (b.val + 1)) = 120 + (c.val + 1) := by
  have hdist : ∀ i : Fin 15, (i.val + 1) * mk1 a b c i
      = (if i = a ∨ i = b then 0 else i.val + 1) + (if i = c then i.val + 1 else 0) := by
    intro i
    unfold mk1
    split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun i _ => hdist i), Finset.sum_add_distrib]
  have h1 := sum_except_two (fun i => i.val + 1) a b hab
  rw [sum_sizes] at h1
  have h2 : ∑ i : Fin 15, (if i = c then i.val + 1 else 0) = c.val + 1 := by simp
  omega

theorem mk2_len (a b c d : Fin 15) (hab : a ≠ b) : ∑ i, mk2 a b c d i = 15 := by
  unfold mk2
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have h1 := sum_except_two (fun _ => 1) a b hab
  rw [sum_one] at h1
  have h2 : ∑ i : Fin 15, (if i = c then (1 : ℕ) else 0) = 1 := by simp
  have h3 : ∑ i : Fin 15, (if i = d then (1 : ℕ) else 0) = 1 := by simp
  omega

theorem mk2_wt (a b c d : Fin 15) (hab : a ≠ b) :
    (∑ i, (i.val + 1) * mk2 a b c d i) + ((a.val + 1) + (b.val + 1))
      = 120 + ((c.val + 1) + (d.val + 1)) := by
  have hdist : ∀ i : Fin 15, (i.val + 1) * mk2 a b c d i
      = (if i = a ∨ i = b then 0 else i.val + 1) + (if i = c then i.val + 1 else 0)
        + (if i = d then i.val + 1 else 0) := by
    intro i
    unfold mk2
    split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun i _ => hdist i), Finset.sum_add_distrib,
    Finset.sum_add_distrib]
  have h1 := sum_except_two (fun i => i.val + 1) a b hab
  rw [sum_sizes] at h1
  have h2 : ∑ i : Fin 15, (if i = c then i.val + 1 else 0) = c.val + 1 := by simp
  have h3 : ∑ i : Fin 15, (if i = d then i.val + 1 else 0) = d.val + 1 := by simp
  omega

/-! ### Where the excess sits -/

/-- The indices carrying more than one part. -/
def Ex (m : Fin 15 → ℕ) : Finset (Fin 15) := (Supp m).filter (fun i => 2 ≤ m i)

theorem mem_Ex {m : Fin 15 → ℕ} {i : Fin 15} : i ∈ Ex m ↔ (i ∈ Supp m ∧ 2 ≤ m i) := by
  simp [Ex]

theorem exc_eq_sum_Ex (m : Fin 15 → ℕ) : Exc m = ∑ i ∈ Ex m, (m i - 1) := by
  rw [Exc]
  refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
  intro i hi hni
  have h1 := one_le_of_mem_Supp hi
  have h2 : ¬ (2 ≤ m i) := fun h => hni (Finset.mem_filter.mpr ⟨hi, h⟩)
  omega

theorem card_Ex_le (m : Fin 15 → ℕ) : (Ex m).card ≤ Exc m := by
  rw [exc_eq_sum_Ex]
  have : ∀ i ∈ Ex m, 1 ≤ m i - 1 := by
    intro i hi
    rw [mem_Ex] at hi
    omega
  calc (Ex m).card = ∑ _i ∈ Ex m, 1 := by rw [Finset.sum_const, smul_eq_mul, mul_one]
    _ ≤ ∑ i ∈ Ex m, (m i - 1) := Finset.sum_le_sum this

theorem excwt_eq_sum_Ex (m : Fin 15 → ℕ) :
    ExcWt m = ∑ i ∈ Ex m, (i.val + 1) * (m i - 1) := by
  rw [ExcWt]
  refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
  intro i hi hni
  have h1 := one_le_of_mem_Supp hi
  have h2 : ¬ (2 ≤ m i) := fun h => hni (Finset.mem_filter.mpr ⟨hi, h⟩)
  have h3 : m i - 1 = 0 := by omega
  rw [h3, mul_zero]

/-- Outside the excess set, a partition has exactly one part of each size in its support. -/
theorem value_off_Ex {m : Fin 15 → ℕ} {i : Fin 15} (hi : i ∈ Supp m) (hni : i ∉ Ex m) :
    m i = 1 := by
  rw [mem_Ex] at hni
  have h1 := one_le_of_mem_Supp hi
  have : ¬ (2 ≤ m i) := fun h2 => hni ⟨hi, h2⟩
  omega

/-! ### Every 13-distinct-size partition is one of the two shapes -/

theorem missing_pair (m : Fin 15 → ℕ) (hc : (Supp m).card = 13) :
    ∃ a b : Fin 15, a.val < b.val ∧ (Supp m)ᶜ = {a, b} := by
  have hcard : ((Supp m)ᶜ).card = 2 := by
    have := Finset.card_compl (Supp m)
    simp only [Fintype.card_fin] at this
    omega
  obtain ⟨x, y, hxy, hset⟩ := Finset.card_eq_two.mp hcard
  rcases lt_trichotomy x.val y.val with h | h | h
  · exact ⟨x, y, h, hset⟩
  · exact absurd (Fin.val_injective h) hxy
  · exact ⟨y, x, h, by rw [hset, Finset.pair_comm]⟩

theorem excwt_value (m : Fin 15 → ℕ) (h : IsPart m) (a b : Fin 15)
    (hab : a.val < b.val) (hset : (Supp m)ᶜ = {a, b}) :
    ExcWt m = (a.val + 1) + (b.val + 1) := by
  obtain ⟨hw, hl⟩ := h
  have hne : a ≠ b := fun hh => by rw [hh] at hab; omega
  have hpair : ∑ i ∈ ((Supp m)ᶜ), (i.val + 1) = (a.val + 1) + (b.val + 1) := by
    rw [hset]; exact Finset.sum_pair hne
  have hsupp := supp_sum_eq m
  rw [Wt_split] at hw
  omega

theorem not_mem_supp_of_mem_pair (m : Fin 15 → ℕ) (a b : Fin 15)
    (hset : (Supp m)ᶜ = {a, b}) : a ∉ Supp m ∧ b ∉ Supp m := by
  have ha : a ∈ (Supp m)ᶜ := by rw [hset]; simp
  have hb : b ∈ (Supp m)ᶜ := by rw [hset]; simp
  exact ⟨by simpa using ha, by simpa using hb⟩

/-- Outside the support is exactly the missing pair. -/
theorem mem_pair_iff (m : Fin 15 → ℕ) (a b : Fin 15) (hset : (Supp m)ᶜ = {a, b})
    (i : Fin 15) : (i = a ∨ i = b) ↔ m i = 0 := by
  constructor
  · intro h
    have h1 : i ∈ (Supp m)ᶜ := by rw [hset]; simpa using h
    have h2 : i ∉ Supp m := by simpa using h1
    by_contra hne
    exact h2 (mem_Supp.mpr hne)
  · intro h
    have h2 : i ∉ Supp m := fun hi => (mem_Supp.mp hi) h
    have h1 : i ∈ (Supp m)ᶜ := by simpa using h2
    rw [hset] at h1
    simpa using h1

theorem eq_mk1 (m : Fin 15 → ℕ) (a b c : Fin 15) (hset : (Supp m)ᶜ = {a, b})
    (hEx : Ex m = {c}) (hmc : m c = 2) : m = mk1 a b c := by
  funext i
  unfold mk1
  by_cases h : i = a ∨ i = b
  · have h0 : m i = 0 := (mem_pair_iff m a b hset i).mp h
    have hic : i ≠ c := by intro hh; rw [hh, hmc] at h0; omega
    simp [h, hic, h0]
  · have hi : i ∈ Supp m := mem_Supp.mpr (fun h0 => h ((mem_pair_iff m a b hset i).mpr h0))
    by_cases hic : i = c
    · subst hic; simp [h, hmc]
    · have hni : i ∉ Ex m := by rw [hEx]; simpa using hic
      have hv := value_off_Ex hi hni
      simp [h, hic, hv]

theorem eq_mk2_same (m : Fin 15 → ℕ) (a b c : Fin 15) (hset : (Supp m)ᶜ = {a, b})
    (hEx : Ex m = {c}) (hmc : m c = 3) : m = mk2 a b c c := by
  funext i
  unfold mk2
  by_cases h : i = a ∨ i = b
  · have h0 : m i = 0 := (mem_pair_iff m a b hset i).mp h
    have hic : i ≠ c := by intro hh; rw [hh, hmc] at h0; omega
    simp [h, hic, h0]
  · have hi : i ∈ Supp m := mem_Supp.mpr (fun h0 => h ((mem_pair_iff m a b hset i).mpr h0))
    by_cases hic : i = c
    · subst hic; simp [h, hmc]
    · have hni : i ∉ Ex m := by rw [hEx]; simpa using hic
      have hv := value_off_Ex hi hni
      simp [h, hic, hv]

theorem eq_mk2_diff (m : Fin 15 → ℕ) (a b c d : Fin 15) (hset : (Supp m)ᶜ = {a, b})
    (hcd : c ≠ d) (hEx : Ex m = {c, d}) (hmc : m c = 2) (hmd : m d = 2) :
    m = mk2 a b c d := by
  funext i
  unfold mk2
  by_cases h : i = a ∨ i = b
  · have h0 : m i = 0 := (mem_pair_iff m a b hset i).mp h
    have hic : i ≠ c := by intro hh; rw [hh, hmc] at h0; omega
    have hid : i ≠ d := by intro hh; rw [hh, hmd] at h0; omega
    simp [h, hic, hid, h0]
  · have hi : i ∈ Supp m := mem_Supp.mpr (fun h0 => h ((mem_pair_iff m a b hset i).mpr h0))
    by_cases hic : i = c
    · subst hic
      simp [h, hcd, hmc]
    · by_cases hid : i = d
      · subst hid
        simp [h, hic, hmd]
      · have hni : i ∉ Ex m := by
          rw [hEx]
          simp only [Finset.mem_insert, Finset.mem_singleton]
          tauto
        have hv := value_off_Ex hi hni
        simp [h, hic, hid, hv]

/-- **Every 13-distinct-size partition of 120 in the box is one of the two shapes.** -/
theorem shape13 (m : Fin 15 → ℕ) (h : IsPart m) (hc : (Supp m).card = 13) :
    (∃ p ∈ P1, m = mk1 p.1 p.2.1 p.2.2) ∨
      (∃ q ∈ P2, m = mk2 q.1 q.2.1 q.2.2.1 q.2.2.2) := by
  obtain ⟨hw, hl⟩ := h
  obtain ⟨a, b, hab, hset⟩ := missing_pair m hc
  have hane : a ∉ Supp m := (not_mem_supp_of_mem_pair m a b hset).1
  have hbne : b ∉ Supp m := (not_mem_supp_of_mem_pair m a b hset).2
  have hexcwt : ExcWt m = (a.val + 1) + (b.val + 1) := excwt_value m ⟨hw, hl⟩ a b hab hset
  have hexc2 : Exc m ≤ 2 := by rw [Len_split, hc] at hl; omega
  have hcard := card_Ex_le m
  -- the excess is nonempty
  have hne : (Ex m).Nonempty := by
    rcases Finset.eq_empty_or_nonempty (Ex m) with he | he
    · exfalso
      rw [excwt_eq_sum_Ex, he, Finset.sum_empty] at hexcwt
      omega
    · exact he
  have hcpos : 1 ≤ (Ex m).card := Finset.card_pos.mpr hne
  -- every excess index lies in the support, so differs from a and b
  have hnotab : ∀ i ∈ Ex m, i ≠ a ∧ i ≠ b := by
    intro i hi
    have hiS : i ∈ Supp m := (Finset.mem_filter.mp hi).1
    exact ⟨fun hh => hane (hh ▸ hiS), fun hh => hbne (hh ▸ hiS)⟩
  rcases Nat.lt_or_ge (Ex m).card 2 with hlt | hge
  · -- a single excess index
    have hone : (Ex m).card = 1 := by omega
    obtain ⟨c, hcs⟩ := Finset.card_eq_one.mp hone
    have hcm : c ∈ Ex m := by rw [hcs]; exact Finset.mem_singleton_self c
    obtain ⟨hca, hcb⟩ := hnotab c hcm
    have hsum : Exc m = m c - 1 := by
      rw [exc_eq_sum_Ex, hcs, Finset.sum_singleton]
    have hwsum : ExcWt m = (c.val + 1) * (m c - 1) := by
      rw [excwt_eq_sum_Ex, hcs, Finset.sum_singleton]
    have hge2 : 2 ≤ m c := (Finset.mem_filter.mp hcm).2
    rcases (by omega : m c = 2 ∨ m c = 3) with hmc | hmc
    · -- one extra part
      rw [hmc] at hwsum
      norm_num at hwsum
      left
      refine ⟨(a, b, c), ?_, eq_mk1 m a b c hset hcs hmc⟩
      simp only [P1, Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    · -- one tripled part
      rw [hmc] at hwsum
      norm_num at hwsum
      right
      refine ⟨(a, b, c, c), ?_, eq_mk2_same m a b c hset hcs hmc⟩
      simp only [P2, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨hab, le_refl _, by omega, hca, hcb, hca, hcb⟩
  · -- two excess indices, each a doubled part
    have htwo : (Ex m).card = 2 := by omega
    obtain ⟨x, y, hxy, hxys⟩ := Finset.card_eq_two.mp htwo
    have hxm : x ∈ Ex m := by rw [hxys]; simp
    have hym : y ∈ Ex m := by rw [hxys]; simp
    have hsum : Exc m = (m x - 1) + (m y - 1) := by
      rw [exc_eq_sum_Ex, hxys, Finset.sum_pair hxy]
    have hwsum : ExcWt m = (x.val + 1) * (m x - 1) + (y.val + 1) * (m y - 1) := by
      rw [excwt_eq_sum_Ex, hxys, Finset.sum_pair hxy]
    have hx2 : 2 ≤ m x := (Finset.mem_filter.mp hxm).2
    have hy2 : 2 ≤ m y := (Finset.mem_filter.mp hym).2
    have hmx : m x = 2 := by omega
    have hmy : m y = 2 := by omega
    rw [hmx, hmy] at hwsum
    norm_num at hwsum
    obtain ⟨hxa, hxb⟩ := hnotab x hxm
    obtain ⟨hya, hyb⟩ := hnotab y hym
    right
    rcases Nat.lt_or_ge x.val y.val with hord | hord
    · refine ⟨(a, b, x, y), ?_, eq_mk2_diff m a b x y hset hxy hxys hmx hmy⟩
      simp only [P2, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨hab, le_of_lt hord, by omega, hxa, hxb, hya, hyb⟩
    · have hyx : y.val < x.val := by
        rcases Nat.lt_or_ge y.val x.val with hh | hh
        · exact hh
        · exact absurd (Fin.val_injective (by omega)) hxy
      have hswap : Ex m = {y, x} := by rw [hxys, Finset.pair_comm]
      refine ⟨(a, b, y, x), ?_, eq_mk2_diff m a b y x hset (Ne.symm hxy) hswap hmy hmx⟩
      simp only [P2, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨hab, le_of_lt hyx, by omega, hya, hyb, hxa, hxb⟩

/-! ### The two shapes really are 13-distinct-size partitions -/

theorem P1_ne (p : Fin 15 × Fin 15 × Fin 15) (hp : p ∈ P1) :
    p.1 ≠ p.2.1 ∧ p.2.2 ≠ p.1 ∧ p.2.2 ≠ p.2.1 := by
  obtain ⟨h1, h2⟩ := mem_P1 hp
  refine ⟨fun hh => ?_, fun hh => ?_, fun hh => ?_⟩ <;>
    (have := congrArg Fin.val hh; omega)

theorem P2_ne (q : Fin 15 × Fin 15 × Fin 15 × Fin 15) (hq : q ∈ P2) :
    q.1 ≠ q.2.1 := by
  obtain ⟨h1, _⟩ := mem_P2 hq
  intro hh
  have := congrArg Fin.val hh
  omega

theorem supp_mk1 (a b c : Fin 15) (hca : c ≠ a) (hcb : c ≠ b) :
    Supp (mk1 a b c) = ({a, b} : Finset (Fin 15))ᶜ := by
  ext i
  rw [mem_Supp, Finset.mem_compl]
  rw [← not_iff_not, not_not, not_not, mk1_zeros a b c hca hcb i]
  simp

theorem supp_mk2 (a b c d : Fin 15) (hca : c ≠ a) (hcb : c ≠ b) (hda : d ≠ a)
    (hdb : d ≠ b) : Supp (mk2 a b c d) = ({a, b} : Finset (Fin 15))ᶜ := by
  ext i
  rw [mem_Supp, Finset.mem_compl]
  rw [← not_iff_not, not_not, not_not, mk2_zeros a b c d hca hcb hda hdb i]
  simp

theorem card_compl_pair (a b : Fin 15) (hab : a ≠ b) :
    (({a, b} : Finset (Fin 15))ᶜ).card = 13 := by
  rw [Finset.card_compl, Finset.card_insert_of_notMem (by simpa using hab),
    Finset.card_singleton]
  rfl

theorem isPart_mk1 (p : Fin 15 × Fin 15 × Fin 15) (hp : p ∈ P1) :
    IsPart (mk1 p.1 p.2.1 p.2.2) ∧ (Supp (mk1 p.1 p.2.1 p.2.2)).card = 13 := by
  obtain ⟨h1, h2⟩ := mem_P1 hp
  obtain ⟨hab, hca, hcb⟩ := P1_ne p hp
  have hw := mk1_wt p.1 p.2.1 p.2.2 hab
  have hl := mk1_len p.1 p.2.1 p.2.2 hab
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · unfold Wt; omega
  · unfold Len; omega
  · rw [supp_mk1 _ _ _ hca hcb, card_compl_pair _ _ hab]

theorem isPart_mk2 (q : Fin 15 × Fin 15 × Fin 15 × Fin 15) (hq : q ∈ P2) :
    IsPart (mk2 q.1 q.2.1 q.2.2.1 q.2.2.2) ∧
      (Supp (mk2 q.1 q.2.1 q.2.2.1 q.2.2.2)).card = 13 := by
  obtain ⟨h1, h2, h3, hca, hcb, hda, hdb⟩ := mem_P2 hq
  have hab := P2_ne q hq
  have hw := mk2_wt q.1 q.2.1 q.2.2.1 q.2.2.2 hab
  have hl := mk2_len q.1 q.2.1 q.2.2.1 q.2.2.2 hab
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · unfold Wt; omega
  · unfold Len; omega
  · rw [supp_mk2 _ _ _ _ hca hcb hda hdb, card_compl_pair _ _ hab]

/-! ### The count -/

theorem pair_eq {a b a' b' : Fin 15} (hab : a.val < b.val) (hab' : a'.val < b'.val)
    (h : ({a, b} : Finset (Fin 15)) = {a', b'}) : a = a' ∧ b = b' := by
  have ha : a = a' ∨ a = b' := by
    have hm : a ∈ ({a', b'} : Finset (Fin 15)) := by rw [← h]; simp
    simpa using hm
  have hb : b = a' ∨ b = b' := by
    have hm : b ∈ ({a', b'} : Finset (Fin 15)) := by rw [← h]; simp
    simpa using hm
  have ha' : a' = a ∨ a' = b := by
    have hm : a' ∈ ({a, b} : Finset (Fin 15)) := by rw [h]; simp
    simpa using hm
  rcases ha with rfl | rfl
  · rcases hb with hb | rfl
    · exact absurd (congrArg Fin.val hb) (by omega)
    · exact ⟨rfl, rfl⟩
  · exfalso
    rcases ha' with hh | hh
    · exact absurd (congrArg Fin.val hh) (by omega)
    · exact absurd (congrArg Fin.val hh) (by omega)

/-- The values of the two-extra shape away from the missing pair. -/
theorem mk2_val (a b c d i : Fin 15) (hi : i ≠ a) (hi' : i ≠ b) :
    mk2 a b c d i = 1 + (if i = c then 1 else 0) + (if i = d then 1 else 0) := by
  unfold mk2
  simp [hi, hi']

theorem ex_mk2 (a b c d : Fin 15) (hca : c ≠ a) (hcb : c ≠ b) (hda : d ≠ a) (hdb : d ≠ b) :
    Ex (mk2 a b c d) = {c, d} := by
  have hsupp := supp_mk2 a b c d hca hcb hda hdb
  ext i
  rw [mem_Ex, hsupp]
  simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or]
  constructor
  · rintro ⟨⟨hia, hib⟩, h2⟩
    rw [mk2_val a b c d i hia hib] at h2
    by_contra hcon
    push_neg at hcon
    rw [if_neg hcon.1, if_neg hcon.2] at h2
    omega
  · intro hi
    have hia : i ≠ a := by rcases hi with rfl | rfl <;> assumption
    have hib : i ≠ b := by rcases hi with rfl | rfl <;> assumption
    refine ⟨⟨hia, hib⟩, ?_⟩
    rw [mk2_val a b c d i hia hib]
    rcases hi with rfl | rfl <;> simp

theorem mk1_inj : ∀ p ∈ P1, ∀ q ∈ P1,
    mk1 p.1 p.2.1 p.2.2 = mk1 q.1 q.2.1 q.2.2 → p = q := by
  intro p hp q hq h
  obtain ⟨hp1, hp2⟩ := mem_P1 hp
  obtain ⟨hq1, hq2⟩ := mem_P1 hq
  obtain ⟨_, hpca, hpcb⟩ := P1_ne p hp
  obtain ⟨_, hqca, hqcb⟩ := P1_ne q hq
  have hs : ({p.1, p.2.1} : Finset (Fin 15))ᶜ = ({q.1, q.2.1} : Finset (Fin 15))ᶜ := by
    rw [← supp_mk1 _ _ _ hpca hpcb, ← supp_mk1 _ _ _ hqca hqcb, h]
  have hs2 : ({p.1, p.2.1} : Finset (Fin 15)) = {q.1, q.2.1} := compl_injective hs
  obtain ⟨e1, e2⟩ := pair_eq hp1 hq1 hs2
  have e3 : p.2.2 = q.2.2 := Fin.val_injective (by rw [hp2, hq2, ← e1, ← e2])
  exact Prod.ext e1 (Prod.ext e2 e3)

theorem mk2_inj : ∀ p ∈ P2, ∀ q ∈ P2,
    mk2 p.1 p.2.1 p.2.2.1 p.2.2.2 = mk2 q.1 q.2.1 q.2.2.1 q.2.2.2 → p = q := by
  intro p hp q hq h
  obtain ⟨hp1, hp2, hp3, hpca, hpcb, hpda, hpdb⟩ := mem_P2 hp
  obtain ⟨hq1, hq2, hq3, hqca, hqcb, hqda, hqdb⟩ := mem_P2 hq
  have hs : ({p.1, p.2.1} : Finset (Fin 15))ᶜ = ({q.1, q.2.1} : Finset (Fin 15))ᶜ := by
    rw [← supp_mk2 _ _ _ _ hpca hpcb hpda hpdb, ← supp_mk2 _ _ _ _ hqca hqcb hqda hqdb, h]
  obtain ⟨e1, e2⟩ := pair_eq hp1 hq1 (compl_injective hs)
  have hex : ({p.2.2.1, p.2.2.2} : Finset (Fin 15)) = {q.2.2.1, q.2.2.2} := by
    rw [← ex_mk2 _ _ _ _ hpca hpcb hpda hpdb, ← ex_mk2 _ _ _ _ hqca hqcb hqda hqdb, h]
  -- read the two extra indices back, ordered
  have hpv : p.2.2.1.val ≤ p.2.2.2.val := hp2
  have hqv : q.2.2.1.val ≤ q.2.2.2.val := hq2
  have hmem1 : p.2.2.1 = q.2.2.1 ∨ p.2.2.1 = q.2.2.2 := by
    have hm : p.2.2.1 ∈ ({q.2.2.1, q.2.2.2} : Finset (Fin 15)) := by rw [← hex]; simp
    simpa using hm
  have hmem2 : p.2.2.2 = q.2.2.1 ∨ p.2.2.2 = q.2.2.2 := by
    have hm : p.2.2.2 ∈ ({q.2.2.1, q.2.2.2} : Finset (Fin 15)) := by rw [← hex]; simp
    simpa using hm
  have hmem3 : q.2.2.1 = p.2.2.1 ∨ q.2.2.1 = p.2.2.2 := by
    have hm : q.2.2.1 ∈ ({p.2.2.1, p.2.2.2} : Finset (Fin 15)) := by rw [hex]; simp
    simpa using hm
  have hmem4 : q.2.2.2 = p.2.2.1 ∨ q.2.2.2 = p.2.2.2 := by
    have hm : q.2.2.2 ∈ ({p.2.2.1, p.2.2.2} : Finset (Fin 15)) := by rw [hex]; simp
    simpa using hm
  have e3 : p.2.2.1 = q.2.2.1 := by
    rcases hmem1 with h1 | h1
    · exact h1
    · rcases hmem3 with h3 | h3
      · exact h3.symm
      · exact Fin.val_injective (by
          have v1 := congrArg Fin.val h1
          have v3 := congrArg Fin.val h3
          omega)
  have e4 : p.2.2.2 = q.2.2.2 := by
    rcases hmem2 with h2 | h2
    · rcases hmem4 with h4 | h4
      · exact Fin.val_injective (by
          have v2 := congrArg Fin.val h2
          have v4 := congrArg Fin.val h4
          omega)
      · exact h4.symm
    · exact h2
  exact Prod.ext e1 (Prod.ext e2 (Prod.ext e3 e4))

/-- The 13-distinct-size partitions, as an explicit finite family. -/
noncomputable def Fam13 : Finset (Fin 15 → ℕ) :=
  P1.image (fun p => mk1 p.1 p.2.1 p.2.2) ∪
    P2.image (fun q => mk2 q.1 q.2.1 q.2.2.1 q.2.2.2)

theorem Fam13_disjoint :
    Disjoint (P1.image (fun p => mk1 p.1 p.2.1 p.2.2))
      (P2.image (fun q => mk2 q.1 q.2.1 q.2.2.1 q.2.2.2)) := by
  rw [Finset.disjoint_left]
  rintro m hm1 hm2
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hm1
  obtain ⟨q, hq, hqe⟩ := Finset.mem_image.mp hm2
  obtain ⟨hab, _⟩ := P1_ne p hp
  have hab2 := P2_ne q hq
  have h14 := mk1_len p.1 p.2.1 p.2.2 hab
  have h15 := mk2_len q.1 q.2.1 q.2.2.1 q.2.2.2 hab2
  rw [hqe] at h15
  omega

/-- **`f_13 = 504`.** -/
theorem Fam13_card : Fam13.card = 504 := by
  rw [Fam13, Finset.card_union_of_disjoint Fam13_disjoint,
    Finset.card_image_of_injOn (fun p hp q hq h => mk1_inj p hp q hq h),
    Finset.card_image_of_injOn (fun p hp q hq h => mk2_inj p hp q hq h),
    P1_card, P2_card]

/-- and the family is exactly the set of 13-distinct-size partitions. -/
theorem mem_Fam13 (m : Fin 15 → ℕ) :
    m ∈ Fam13 ↔ (IsPart m ∧ (Supp m).card = 13) := by
  constructor
  · intro hm
    rcases Finset.mem_union.mp hm with h | h
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp h
      exact isPart_mk1 p hp
    · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp h
      exact isPart_mk2 q hq
  · rintro ⟨h1, h2⟩
    rcases shape13 m h1 h2 with ⟨p, hp, rfl⟩ | ⟨q, hq, rfl⟩
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨p, hp, rfl⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨q, hq, rfl⟩)

/-! ### Four-colourings of a set of distinct sizes

A colouring assigns one of four colours to each distinct part size.  Recording the classes of
colours 2, 3 and 4 as `(A, B, C)` (everything else gets colour 1) makes a colouring exactly a
triple of pairwise disjoint subsets of prescribed sizes. -/

def Cols (S : Finset (Fin 15)) (u v w : ℕ) :
    Finset (Finset (Fin 15) × Finset (Fin 15) × Finset (Fin 15)) :=
  (S.powersetCard u).biUnion (fun A =>
    ((S \ A).powersetCard v).biUnion (fun B =>
      (((S \ A) \ B).powersetCard w).image (fun C => (A, B, C))))

theorem card_Cols (S : Finset (Fin 15)) (u v w : ℕ) :
    (Cols S u v w).card
      = S.card.choose u * ((S.card - u).choose v * (S.card - u - v).choose w) := by
  rw [Cols, Finset.card_biUnion]
  · have hA : ∀ A ∈ S.powersetCard u,
        (((S \ A).powersetCard v).biUnion (fun B =>
          (((S \ A) \ B).powersetCard w).image (fun C => (A, B, C)))).card
          = (S.card - u).choose v * (S.card - u - v).choose w := by
      intro A hA
      obtain ⟨hAS, hAc⟩ := Finset.mem_powersetCard.mp hA
      have hcardA : (S \ A).card = S.card - u := by
        rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hAS, hAc]
      rw [Finset.card_biUnion]
      · have hB : ∀ B ∈ (S \ A).powersetCard v,
            ((((S \ A) \ B).powersetCard w).image (fun C => (A, B, C))).card
              = (S.card - u - v).choose w := by
          intro B hB
          obtain ⟨hBS, hBc⟩ := Finset.mem_powersetCard.mp hB
          rw [Finset.card_image_of_injective _ (by intro x y h; simpa using h),
            Finset.card_powersetCard, Finset.card_sdiff, Finset.inter_eq_left.mpr hBS,
            hcardA, hBc]
        rw [Finset.sum_congr rfl hB, Finset.sum_const, Finset.card_powersetCard, hcardA,
          smul_eq_mul]
      · intro x hx y hy hxy
        simp only [Function.onFun]
        rw [Finset.disjoint_left]
        rintro t ht ht'
        obtain ⟨c1, _, e1⟩ := Finset.mem_image.mp ht
        obtain ⟨c2, _, e2⟩ := Finset.mem_image.mp ht'
        rw [← e1] at e2
        exact hxy (congrArg (fun z => z.2.1) e2).symm
    rw [Finset.sum_congr rfl hA, Finset.sum_const, Finset.card_powersetCard, smul_eq_mul]
  · intro x hx y hy hxy
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    rintro t ht ht'
    obtain ⟨b1, _, e1⟩ := Finset.mem_biUnion.mp ht
    obtain ⟨b2, _, e2⟩ := Finset.mem_biUnion.mp ht'
    obtain ⟨c1, _, f1⟩ := Finset.mem_image.mp e1
    obtain ⟨c2, _, f2⟩ := Finset.mem_image.mp e2
    rw [← f1] at f2
    exact hxy (congrArg (fun z => z.1) f2).symm

/-- A colouring needs at least `u + v + w` sizes to colour. -/
theorem cols_eq_empty (S : Finset (Fin 15)) (u v w : ℕ) (h : S.card < u + v + w) :
    (Cols S u v w).card = 0 := by
  rw [card_Cols]
  rcases Nat.lt_or_ge S.card u with h1 | h1
  · rw [Nat.choose_eq_zero_of_lt h1, zero_mul]
  · rcases Nat.lt_or_ge (S.card - u) v with h2 | h2
    · rw [Nat.choose_eq_zero_of_lt h2, zero_mul, mul_zero]
    · have h3 : S.card - u - v < w := by omega
      rw [Nat.choose_eq_zero_of_lt h3, mul_zero, mul_zero]

/-! ### The coefficient array -/

/-- All partitions of the box, as a `Finset`. -/
def PartsF : Finset (Fin 15 → ℕ) :=
  (Fintype.piFinset (fun _ : Fin 15 => Finset.range 16)).filter (fun m => Wt m = 120 ∧ Len m ≤ 15)

theorem mem_PartsF (m : Fin 15 → ℕ) : m ∈ PartsF ↔ IsPart m := by
  constructor
  · intro h; exact (Finset.mem_filter.mp h).2
  · intro h
    refine Finset.mem_filter.mpr ⟨?_, h⟩
    rw [Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_range]
    have hle : m i ≤ Len m :=
      Finset.single_le_sum (f := m) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    have := h.2
    omega

/-- The coefficient of `x^u y^v z^w`: the number of coloured partitions with `u` sizes of the
second colour, `v` of the third and `w` of the fourth. -/
def Coeff (u v w : ℕ) : ℕ := ∑ m ∈ PartsF, (Cols (Supp m) u v w).card

/-- The all-ones vector: the partition `1 + 2 + ⋯ + 15`. -/
def ones : Fin 15 → ℕ := fun _ => 1

theorem supp_ones : Supp ones = univ := by
  ext i; simp [Supp, ones]

theorem isPart_ones : IsPart ones := by
  constructor
  · unfold Wt ones; simpa using sum_sizes
  · unfold Len ones; simpa using sum_one

theorem card_supp_le (m : Fin 15 → ℕ) : (Supp m).card ≤ 15 := by
  have := Finset.card_le_card (Finset.subset_univ (Supp m))
  simpa using this

theorem ones_not_mem_Fam13 : ones ∉ Fam13 := by
  intro h
  have := ((mem_Fam13 ones).mp h).2
  rw [supp_ones] at this
  simp at this

theorem filter_ge (k : ℕ) (hk : 13 ≤ k) (hk' : k ≤ 15) :
    PartsF.filter (fun m => k ≤ (Supp m).card)
      = if k = 13 then insert ones Fam13 else {ones} := by
  ext m
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hm, hcard⟩
    have hp : IsPart m := (mem_PartsF m).mp hm
    have hle := card_supp_le m
    have h3 : (Supp m).card = 13 ∨ (Supp m).card = 14 ∨ (Supp m).card = 15 := by omega
    rcases h3 with h | h | h
    · have hk13 : k = 13 := by omega
      rw [if_pos hk13]
      exact Finset.mem_insert_of_mem ((mem_Fam13 m).mpr ⟨hp, h⟩)
    · exact absurd (card14 m hp h) (by simp)
    · have hone : m = ones := card15 m hp h
      by_cases hk13 : k = 13
      · rw [if_pos hk13, hone]; exact Finset.mem_insert_self _ _
      · rw [if_neg hk13, hone]; exact Finset.mem_singleton_self _
  · intro h
    by_cases hk13 : k = 13
    · rw [if_pos hk13] at h
      rcases Finset.mem_insert.mp h with rfl | h
      · exact ⟨(mem_PartsF _).mpr isPart_ones, by rw [supp_ones]; simpa using hk'⟩
      · obtain ⟨hp, hc⟩ := (mem_Fam13 m).mp h
        exact ⟨(mem_PartsF m).mpr hp, by omega⟩
    · rw [if_neg hk13] at h
      rw [Finset.mem_singleton.mp h]
      exact ⟨(mem_PartsF _).mpr isPart_ones, by rw [supp_ones]; simpa using hk'⟩

theorem coeff_split (u v w : ℕ) (hk : 13 ≤ u + v + w) (hk' : u + v + w ≤ 15) :
    Coeff u v w = ∑ m ∈ (if u + v + w = 13 then insert ones Fam13 else {ones}),
      (Cols (Supp m) u v w).card := by
  rw [Coeff, ← filter_ge (u + v + w) hk hk']
  refine (Finset.sum_filter_of_ne ?_).symm
  intro m hm hne
  by_contra hcon
  push_neg at hcon
  exact hne (cols_eq_empty (Supp m) u v w (by omega))

theorem coeff_10 : Coeff 10 2 2 = 90090 := by
  rw [coeff_split 10 2 2 (by norm_num) (by norm_num), if_neg (by norm_num),
    Finset.sum_singleton, supp_ones, card_Cols]
  simp only [Finset.card_univ, Fintype.card_fin]
  simp only [Nat.choose_eq_descFactorial_div_factorial]
  norm_num

theorem coeff_9 : Coeff 9 3 3 = 100100 := by
  rw [coeff_split 9 3 3 (by norm_num) (by norm_num), if_neg (by norm_num),
    Finset.sum_singleton, supp_ones, card_Cols]
  simp only [Finset.card_univ, Fintype.card_fin]
  simp only [Nat.choose_eq_descFactorial_div_factorial]
  norm_num



/-! ### The coefficient at `(11,1,1)`

`PartsF` is a filter over `Fintype.piFinset (fun _ : Fin 15 => range 16)` — `16^15`
elements — and it is COMPUTABLE, so anything that `whnf`s it tries to build that Finset.
Measured: instantiating `Finset.sum_filter_add_sum_filter_not` DIRECTLY at `PartsF.filter …`
drives the elaborator past 11 GB.  Two habits keep that from happening:

* name the set with an OPAQUE `def` (`S`) and route every fact through `mem_S`;
* prove each manipulation over an ARBITRARY `Finset` and INSTANTIATE it with the statement
  ascribed — instantiating a proved lemma is substitution, never normalisation.
-/

/-- The partitions contributing to a coefficient of total order 13. -/
def S : Finset (Fin 15 → ℕ) := PartsF.filter (fun m => 13 ≤ (Supp m).card)

theorem mem_S (m : Fin 15 → ℕ) : m ∈ S ↔ (IsPart m ∧ 13 ≤ (Supp m).card) := by
  rw [S, Finset.mem_filter, mem_PartsF]

/-- The split, proved over an ARBITRARY `s` so it can be instantiated at `S` safely. -/
theorem split_at (s : Finset (Fin 15 → ℕ)) (u v w : ℕ) :
    ∑ m ∈ s, (Cols (Supp m) u v w).card
      = (∑ m ∈ s.filter (fun m => (Supp m).card = 13), (Cols (Supp m) u v w).card)
        + ∑ m ∈ s.filter (fun m => ¬ (Supp m).card = 13), (Cols (Supp m) u v w).card :=
  (Finset.sum_filter_add_sum_filter_not s _ _).symm

theorem filter13_eq : S.filter (fun m => (Supp m).card = 13) = Fam13 := by
  ext m
  simp only [Finset.mem_filter, mem_S]
  constructor
  · rintro ⟨⟨hp, _⟩, hc⟩
    exact (mem_Fam13 m).mpr ⟨hp, hc⟩
  · intro h
    obtain ⟨hp, hc⟩ := (mem_Fam13 m).mp h
    exact ⟨⟨hp, by omega⟩, hc⟩

theorem filter13_ne :
    S.filter (fun m => ¬ (Supp m).card = 13) = ({ones} : Finset (Fin 15 → ℕ)) := by
  ext m
  simp only [Finset.mem_filter, Finset.mem_singleton, mem_S]
  constructor
  · rintro ⟨⟨hp, hge⟩, hne⟩
    have hle := card_supp_le m
    have h3 : (Supp m).card = 14 ∨ (Supp m).card = 15 := by omega
    rcases h3 with h | h
    · exact absurd (card14 m hp h) (by simp)
    · exact card15 m hp h
  · rintro rfl
    refine ⟨⟨isPart_ones, ?_⟩, ?_⟩
    · rw [supp_ones]; simp
    · rw [supp_ones]; simp

theorem coeff_base : Coeff 11 1 1 = ∑ m ∈ S, (Cols (Supp m) 11 1 1).card := by
  rw [Coeff, S]
  refine (Finset.sum_filter_of_ne ?_).symm
  intro m hm hne
  by_contra hcon
  push_neg at hcon
  exact hne (cols_eq_empty (Supp m) 11 1 1 (by omega))

/-- `Coeff 11 1 1` splits into the 13-support family and the all-ones partition. -/
theorem coeff_split_two : Coeff 11 1 1
      = (∑ m ∈ Fam13, (Cols (Supp m) 11 1 1).card)
        + ∑ m ∈ ({ones} : Finset (Fin 15 → ℕ)), (Cols (Supp m) 11 1 1).card := by
  rw [coeff_base, split_at S 11 1 1, filter13_eq, filter13_ne]

/-- Every 13-support partition contributes the same count. -/
theorem cols_const_on_Fam13 : ∀ m ∈ Fam13, (Cols (Supp m) 11 1 1).card = 156 := by
  intro m hm
  rw [card_Cols, ((mem_Fam13 m).mp hm).2]
  simp only [Nat.choose_eq_descFactorial_div_factorial]
  norm_num

/-- The 13-support family contributes `504 × 156`.

`Finset.sum_congr` is used as an ASCRIBED TERM rather than a rewrite: as a rewrite it forced
unification against `Fam13`'s definition and drove the elaborator past 7.6 GB; ascribed, the
same step costs seconds. -/
theorem sum_fam13 : (∑ m ∈ Fam13, (Cols (Supp m) 11 1 1).card) = 78624 := by
  have h : (∑ m ∈ Fam13, (Cols (Supp m) 11 1 1).card) = ∑ _m ∈ Fam13, 156 :=
    Finset.sum_congr rfl cols_const_on_Fam13
  rw [h, Finset.sum_const, Fam13_card, smul_eq_mul]

/-- The all-ones partition contributes `C(15,11)·C(4,1)·C(3,1) = 16380`. -/
theorem sum_ones : (∑ m ∈ ({ones} : Finset (Fin 15 → ℕ)), (Cols (Supp m) 11 1 1).card)
    = 16380 := by
  rw [Finset.sum_singleton, supp_ones, card_Cols]
  simp only [Finset.card_univ, Fintype.card_fin]
  simp only [Nat.choose_eq_descFactorial_div_factorial]
  norm_num

/-- **The third coefficient.** -/
theorem coeff_11 : Coeff 11 1 1 = 95004 := by
  rw [coeff_split_two, sum_fam13, sum_ones]

/-- **The unimodality conjecture is FALSE.**  The three adjacent coefficients go DOWN then
UP: `Coeff 11 1 1 = 95004`, `Coeff 10 2 2 = 90090`, `Coeff 9 3 3 = 100100`, so the middle
one is a strict local MINIMUM. -/
theorem main : Coeff 10 2 2 < Coeff 11 1 1 ∧ Coeff 10 2 2 < Coeff 9 3 3 := by
  rw [coeff_11, coeff_10, coeff_9]
  norm_num

end Principia.MathDB.P345259
