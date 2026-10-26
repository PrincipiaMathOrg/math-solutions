import Mathlib.Tactic

set_option autoImplicit false

/-!
# MathDB 348827 — the restricted fractional-partition sequence, and its unique bimodal case

Write-up: `mathdb-open-problems/problems/348827/solution.tex` on the `mathdb-results`
branch of `antoshashakov/Principia-Math-In-Progress`.  It **confirms Conjecture 1.0.4 of
Hoelscher–Palsson** and sharpens it to an exact classification.

For an integer `j > 2` let `f j k` be the number of subsets of the odd numbers
`{1, 3, …, 2j-1}` whose sum is `k * j`.  The conjecture asks whether the sequence
`(f j 1, …, f j (j-1))` is always unimodal *or* bimodal.  The answer is yes, and the
bimodal case is unique: the sequence is **unimodal for every `j > 2` except `j = 6`**,
where it is `(1, 3, 2, 3, 1)` — two peaks with a strict valley between them.

## How the proof is organised here

The subsets are counted directly (`c`, a `Finset.powerset` filter), so the object is the
conjecture's own and nothing is encoded away.  Two bridges make it tractable:

* `c_succ` — splitting the powerset of `range (j+1)` on whether it contains `j` gives the
  write-up's recurrence `a_j(n) = a_{j-1}(n) + a_{j-1}(n - (2j-1))`.
* `c_eq_coeff` — hence `c j n` is the `n`-th coefficient of `∏_{i<j} (1 + q^{2i+1})`,
  carried as the list `Acoef j`.  This is what makes the finite range **decidable**: the
  list is built by one linear pass per factor, so the kernel evaluates `Acoef 26` outright,
  whereas `decide` on the powerset itself runs out of room around `j = 14`.

`c_compl` is the write-up's symmetry `a_j(n) = a_j(j² - n)`, proved by complementation
inside `range j`; it yields the palindrome `f j k = f j (j - k)`.  `unimodal_of_half` is
the structural step: a palindromic sequence that rises on its first half is unimodal on
the whole range.  So only the first half ever has to be checked, which is exactly the
quantity the write-up tabulates as

  `d_j = min_{1 ≤ k < ⌊j/2⌋} (a_j((k+1)j) - a_j(kj))`.

`halfMono_small` discharges `3 ≤ j ≤ 26` by kernel computation — the write-up's table is
**reproduced, not assumed** — and `d_6 < 0` is precisely why `j = 6` is excluded there.

## What is carried

`Setup.pakPanova` alone: Pak–Panova's Theorem 5.2, quoted by the write-up for `j ≥ 27`,
in the form the argument consumes (`c j` is weakly increasing on `[26, j²/2]`).  The
index bookkeeping that puts every `kj` inside that window is proved, not carried.

Python check: `Campaigns/MathDB-Formalization/verify_348827.py` — exact integers; it
counts `f j k` by direct subset enumeration against the product coefficients, reproduces
all 23 tabulated `d_j`, and confirms `d_6 = -1` is the only negative entry and `d_10 = 0`
the only zero.
-/

namespace Principia.MathDB.P348827

open Finset

/-! ### The counting function -/

/-- `c j n` — the number of subsets of `{1, 3, …, 2j-1}` whose elements sum to `n`. -/
def c (j n : ℕ) : ℕ :=
  (((range j).powerset).filter (fun S => ∑ i ∈ S, (2 * i + 1) = n)).card

/-- `f j k` — the write-up's `f_j(k)`: subsets of `{1, 3, …, 2j-1}` summing to `k * j`. -/
def f (j k : ℕ) : ℕ := c j (k * j)

lemma c_zero (n : ℕ) : c 0 n = if n = 0 then 1 else 0 := by
  unfold c
  rw [range_zero, powerset_empty]
  by_cases h : n = 0 <;> simp [h, filter_singleton, eq_comm]

/-- Splitting the powerset on whether it contains `j` gives the write-up's recurrence. -/
lemma c_succ (j n : ℕ) :
    c (j + 1) n = c j n + (if 2 * j + 1 ≤ n then c j (n - (2 * j + 1)) else 0) := by
  have hj : j ∉ range j := by simp
  have hsum : ∀ a ∈ (range j).powerset,
      (∑ i ∈ insert j a, (2 * i + 1)) = (2 * j + 1) + ∑ i ∈ a, (2 * i + 1) := fun a ha =>
    Finset.sum_insert (fun h => hj (mem_powerset.1 ha h))
  unfold c
  rw [range_add_one, powerset_insert, filter_union, card_union_of_disjoint]
  · congr 1
    rw [filter_image, card_image_of_injOn]
    · rw [filter_congr (fun a ha => by rw [hsum a ha])]
      split_ifs with h
      · exact congrArg _ (filter_congr (fun a _ => by constructor <;> intro <;> omega))
      · rw [filter_false_of_mem (fun a _ hc => h (by omega)), card_empty]
    · intro a ha b hb hab
      simp only [coe_filter, Set.mem_setOf_eq, mem_powerset] at ha hb
      have ja : j ∉ a := fun h => hj (ha.1 h)
      have jb : j ∉ b := fun h => hj (hb.1 h)
      rw [← erase_insert ja, ← erase_insert jb, hab]
  · rw [Finset.disjoint_left]
    intro S hS hS'
    simp only [mem_filter, mem_powerset, mem_image] at hS hS'
    obtain ⟨⟨t, _, rfl⟩, _⟩ := hS'
    exact hj (hS.1 (mem_insert_self j t))

/-! ### The coefficient list

`Acoef j` holds the coefficients of `∏_{i<j} (1 + q^{2i+1})`.  Each factor costs one
linear pass, so the kernel can evaluate the whole finite range of the write-up's table.
-/

/-- Coefficients of `(1 + q^w) * L`, given those of `L`. -/
def conv (w : ℕ) (L : List ℕ) : List ℕ :=
  List.zipWith (· + ·) (L ++ List.replicate w 0) (List.replicate w 0 ++ L)

/-- Coefficients of `∏_{i<j} (1 + q^{2i+1})`. -/
def Acoef : ℕ → List ℕ
  | 0 => [1]
  | j + 1 => conv (2 * j + 1) (Acoef j)

lemma getD_zero {L : List ℕ} {n : ℕ} (h : L.length ≤ n) : L.getD n 0 = 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]; rfl

lemma getD_append_replicate (L : List ℕ) (w n : ℕ) :
    (L ++ List.replicate w 0).getD n 0 = L.getD n 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append, List.getElem?_replicate]
  split
  · rfl
  · rw [List.getElem?_eq_none (by omega)]
    split <;> rfl

lemma getD_replicate_append (L : List ℕ) (w n : ℕ) :
    (List.replicate w 0 ++ L).getD n 0 = if w ≤ n then L.getD (n - w) 0 else 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append, List.getElem?_replicate,
    List.length_replicate]
  split <;> split <;> simp_all <;> omega

lemma getD_zipWith_add (a b : List ℕ) (n : ℕ) (hab : a.length = b.length) :
    (List.zipWith (· + ·) a b).getD n 0 = a.getD n 0 + b.getD n 0 := by
  rcases lt_or_ge n a.length with h | h
  · rw [List.getD_eq_getElem?_getD, List.getElem?_zipWith,
      List.getElem?_eq_getElem h, List.getElem?_eq_getElem (hab ▸ h)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h,
      List.getElem?_eq_getElem (hab ▸ h)]
  · rw [getD_zero (by simp [hab]; omega), getD_zero h, getD_zero (by omega)]

lemma conv_getD (w n : ℕ) (L : List ℕ) :
    (conv w L).getD n 0 = L.getD n 0 + (if w ≤ n then L.getD (n - w) 0 else 0) := by
  unfold conv
  rw [getD_zipWith_add _ _ _ (by simp [Nat.add_comm]), getD_append_replicate,
    getD_replicate_append]

/-- The bridge: the subset count *is* the coefficient of the product. -/
lemma c_eq_coeff (j n : ℕ) : c j n = (Acoef j).getD n 0 := by
  induction j generalizing n with
  | zero =>
    rw [c_zero]
    match n with
    | 0 => rfl
    | _ + 1 => simp [Acoef]
  | succ m ih => rw [c_succ, Acoef, conv_getD]; simp only [ih]

lemma f_eq_coeff (j k : ℕ) : f j k = (Acoef j).getD (k * j) 0 := c_eq_coeff j (k * j)

/-! ### Symmetry: `a_j(n) = a_j(j² - n)` -/

lemma sum_odd_range (j : ℕ) : ∑ i ∈ range j, (2 * i + 1) = j * j := by
  induction j with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih]; ring

/-- Complementation inside `range j` sends a subset of sum `n` to one of sum `j² - n`. -/
lemma c_compl (j n : ℕ) (hn : n ≤ j * j) : c j n = c j (j * j - n) := by
  unfold c
  refine Finset.card_nbij' (fun S => range j \ S) (fun S => range j \ S) ?_ ?_ ?_ ?_
  · intro S hS
    simp only [coe_filter, Set.mem_setOf_eq, mem_powerset] at hS ⊢
    refine ⟨sdiff_subset, ?_⟩
    have := Finset.sum_sdiff (f := fun i => 2 * i + 1) hS.1
    rw [hS.2, sum_odd_range] at this
    omega
  · intro S hS
    simp only [coe_filter, Set.mem_setOf_eq, mem_powerset] at hS ⊢
    refine ⟨sdiff_subset, ?_⟩
    have := Finset.sum_sdiff (f := fun i => 2 * i + 1) hS.1
    rw [hS.2, sum_odd_range] at this
    omega
  · intro S hS
    simp only [coe_filter, Set.mem_setOf_eq, mem_powerset] at hS
    exact Finset.sdiff_sdiff_eq_self hS.1
  · intro S hS
    simp only [coe_filter, Set.mem_setOf_eq, mem_powerset] at hS
    exact Finset.sdiff_sdiff_eq_self hS.1

/-- The palindrome the write-up derives from the symmetry. -/
lemma f_palindrome (j k : ℕ) (hk : k ≤ j) : f j k = f j (j - k) := by
  unfold f
  rw [c_compl j (k * j) (Nat.mul_le_mul_right j hk)]
  congr 1
  cases Nat.le.dest hk with
  | intro d hd => subst hd; simp [Nat.add_mul]

/-! ### Unimodality from half-monotonicity -/

/-- `g` rises weakly to a peak at `m`, then falls weakly, throughout `[lo, hi]`. -/
def Unimodal (g : ℕ → ℕ) (lo hi : ℕ) : Prop :=
  ∃ m, lo ≤ m ∧ m ≤ hi ∧
    (∀ p q, lo ≤ p → p ≤ q → q ≤ m → g p ≤ g q) ∧
    (∀ p q, m ≤ p → p ≤ q → q ≤ hi → g q ≤ g p)

/-- Two unimodal runs meeting at a shared index — the conjecture's second alternative. -/
def Bimodal (g : ℕ → ℕ) (lo hi : ℕ) : Prop :=
  ∃ m, lo ≤ m ∧ m ≤ hi ∧ Unimodal g lo m ∧ Unimodal g m hi

/-- Single steps chain into monotonicity across an interval. -/
lemma step_chain (g : ℕ → ℕ) (M : ℕ) (h : ∀ k, 1 ≤ k → k + 1 ≤ M → g k ≤ g (k + 1)) :
    ∀ p q, 1 ≤ p → p ≤ q → q ≤ M → g p ≤ g q := by
  intro p q hp hpq hqM
  induction q with
  | zero => omega
  | succ r ih =>
    rcases Nat.lt_or_ge p (r + 1) with hlt | hge
    · exact le_trans (ih (by omega) (by omega)) (h r (by omega) hqM)
    · have : p = r + 1 := by omega
      exact this ▸ le_refl _

/-- **The structural step.**  A palindromic sequence that rises on its first half is
unimodal on the whole range — so only the first half is ever checked. -/
lemma unimodal_of_half (g : ℕ → ℕ) (j : ℕ) (hj : 2 < j)
    (hpal : ∀ k, 1 ≤ k → k ≤ j - 1 → g k = g (j - k))
    (hmono : ∀ k, 1 ≤ k → k + 1 ≤ j / 2 → g k ≤ g (k + 1)) :
    Unimodal g 1 (j - 1) := by
  have hstep : ∀ k, 1 ≤ k → k + 1 ≤ j - j / 2 → g k ≤ g (k + 1) := by
    intro k hk hkM
    by_cases h : k + 1 ≤ j / 2
    · exact hmono k hk h
    · have hk2 : k = j / 2 := by omega
      have hodd : j - (k + 1) = k := by omega
      rw [hpal (k + 1) (by omega) (by omega), hodd]
  have hrise := step_chain g (j - j / 2) hstep
  refine ⟨j / 2, by omega, by omega, ?_, ?_⟩
  · intro p q hp hpq hq
    exact hrise p q hp hpq (by omega)
  · intro p q hp hpq hq
    rw [hpal p (by omega) (by omega), hpal q (by omega) (by omega)]
    exact hrise (j - q) (j - p) (by omega) (by omega) (by omega)

/-! ### The finite range `3 ≤ j ≤ 26`, checked by the kernel -/

set_option maxRecDepth 4000000 in
/-- The write-up's `d_j ≥ 0` for `3 ≤ j ≤ 26`, `j ≠ 6`, **recomputed** by the kernel from
the coefficient list rather than taken from its printed table. -/
lemma halfMono_small (j : ℕ) (h3 : 3 ≤ j) (h26 : j ≤ 26) (h6 : j ≠ 6) :
    ∀ k ∈ Finset.Ico 1 (j / 2), (Acoef j).getD (k * j) 0 ≤ (Acoef j).getD ((k + 1) * j) 0 := by
  interval_cases j <;> first | omega | decide

/-! ### The carry -/

/-- The single carried input: **Pak–Panova, Theorem 5.2**, quoted by the write-up for
`j ≥ 27` — for such `j` the coefficient sequence of `∏_{i<j}(1 + q^{2i+1})` is strictly
unimodal on `[26, j² - 26]`, hence weakly increasing up to the centre `j²/2`.  This is
the statement in the form the argument below consumes. -/
structure Setup where
  pakPanova : ∀ j m n, 27 ≤ j → 26 ≤ m → m ≤ n → 2 * n ≤ j * j → c j m ≤ c j n

namespace Setup

/-- Every `k j` with `1 ≤ k` and `k + 1 ≤ j/2` lands inside Pak–Panova's window. -/
lemma halfMono_large (S : Setup) (j : ℕ) (hj : 27 ≤ j) :
    ∀ k, 1 ≤ k → k + 1 ≤ j / 2 → f j k ≤ f j (k + 1) := by
  intro k hk hkj
  exact S.pakPanova j (k * j) ((k + 1) * j) hj (by nlinarith) (by nlinarith)
    (by have : 2 * (k + 1) ≤ j := by omega
        nlinarith)

/-- **The sharp classification.**  Every `j > 2` other than `6` gives a unimodal
sequence. -/
theorem unimodal_of_ne_six (S : Setup) (j : ℕ) (hj : 2 < j) (h6 : j ≠ 6) :
    Unimodal (f j) 1 (j - 1) := by
  refine unimodal_of_half (f j) j hj (fun k _ hk => f_palindrome j k (by omega)) ?_
  intro k hk hkj
  by_cases h : 27 ≤ j
  · exact S.halfMono_large j h k hk hkj
  · have := halfMono_small j (by omega) (by omega) h6 k (by simp; omega)
    rw [f_eq_coeff, f_eq_coeff]
    exact this

end Setup

/-! ### `j = 6`: the unique bimodal case -/

lemma f_six : f 6 1 = 1 ∧ f 6 2 = 3 ∧ f 6 3 = 2 ∧ f 6 4 = 3 ∧ f 6 5 = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rw [f_eq_coeff] <;> decide

/-- `(1, 3, 2, 3, 1)` has a strict interior valley, so it is **not** unimodal. -/
theorem six_not_unimodal : ¬ Unimodal (f 6) 1 5 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := f_six
  rintro ⟨m, hm1, hm5, hrise, hfall⟩
  by_cases h : m ≤ 3
  · have := hfall 3 4 h (by omega) (by omega)
    omega
  · have := hrise 2 3 (by omega) (by omega) (by omega)
    omega

/-- …but it splits at the valley into two unimodal runs, so it **is** bimodal — which is
what makes Hoelscher–Palsson's disjunction true at `j = 6`. -/
theorem six_bimodal : Bimodal (f 6) 1 5 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := f_six
  refine ⟨3, by omega, by omega, ⟨2, by omega, by omega, ?_, ?_⟩,
    ⟨4, by omega, by omega, ?_, ?_⟩⟩
  all_goals
    intro p q hp hpq hq
    have hp' : p ≤ q := hpq
    have hq' := le_trans hpq hq
    interval_cases p <;> interval_cases q <;> omega

/-- At `j = 10` the sequence has three equal central entries — the write-up's other
near-miss, and the reason `d_10 = 0` rather than positive. -/
lemma f_ten_plateau : f 10 4 = 20 ∧ f 10 5 = 20 ∧ f 10 6 = 20 := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [f_eq_coeff] <;> decide

/-! ### The conjecture -/

/-- **Hoelscher–Palsson Conjecture 1.0.4 holds.**  For every `j > 2` the sequence
`(f j 1, …, f j (j-1))` is unimodal or bimodal.

Read on its own this is the weaker half: `Bimodal` follows from `Unimodal` (take
`m = hi`), so the disjunction is not where the content lies.  `classification` below is
the sharp statement, and `six_not_unimodal` is what makes it sharp. -/
theorem Setup.conjecture (S : Setup) (j : ℕ) (hj : 2 < j) :
    Unimodal (f j) 1 (j - 1) ∨ Bimodal (f j) 1 (j - 1) := by
  by_cases h6 : j = 6
  · subst h6; exact Or.inr six_bimodal
  · exact Or.inl (S.unimodal_of_ne_six j hj h6)

/-- **The sharp classification: `j = 6` is the unique non-unimodal case.**  For every
`j > 2` the sequence fails to be unimodal exactly when `j = 6`, where it is the bimodal
`(1, 3, 2, 3, 1)`. -/
theorem Setup.classification (S : Setup) (j : ℕ) (hj : 2 < j) :
    ¬ Unimodal (f j) 1 (j - 1) ↔ j = 6 := by
  constructor
  · intro h
    by_contra h6
    exact h (S.unimodal_of_ne_six j hj h6)
  · rintro rfl
    exact six_not_unimodal

end Principia.MathDB.P348827
