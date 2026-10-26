import Principia.MathDB.Problem367940Euler

/-!
# MathDB #367940 — words satisfying the maximum-run inequalities

Write-up: `antoshashakov/Principia-Math-In-Progress`, branch `mathdb-results`,
`mathdb-open-problems/problems/367940/solution.tex`, §2.  A word `y` of length `2j+1` is
*admissible* (`Adm`) when, writing `aᵢ = y(2i)` and `bᵢ = y(2i−1)`,
`a₀ < a₁ < ⋯ < a_j` and `aᵢ ≤ bᵢ` — the write-up's (3), in the form
`y(2i) < y(2i+2) ≤ y(2i+1)`.  This module counts admissible words with letters in `{0, …, m−1}`:

* `G_eq`: with first letter `v < m` there are `e_j(1, …, m−1−v)` of them (peel `a₀ b₁`: the rest
  is admissible with first letter `c > v`, and `b₁` has `m − c` choices);
* `T_eq`: in total there are `V j m = ∑_{u<m} e_j(1, …, u)`.

The write-up counts the same words with `a₀` removed, `T_j(m) = e_j(1, …, m)` in its (5).  The
fiber count over Fubini rankings is the consumer.
-/

namespace Principia.MathDB.P367940

open Finset

/-- A word `Fin n → Fin m`, read as a sequence of naturals (zero past the end). -/
def wd {n m : ℕ} (y : Fin n → Fin m) (p : ℕ) : ℕ := if h : p < n then (y ⟨p, h⟩ : ℕ) else 0

/-- The inequalities `y(2i) < y(2i+2) ≤ y(2i+1)` for `i < j`. -/
def Adm (j : ℕ) (y : ℕ → ℕ) : Prop :=
  ∀ i < j, y (2 * i) < y (2 * i + 2) ∧ y (2 * i + 2) ≤ y (2 * i + 1)

theorem wd_lt {n m : ℕ} (y : Fin n → Fin m) (p : ℕ) (hp : p < n) : wd y p < m := by
  unfold wd
  rw [dif_pos hp]
  exact (y _).isLt

theorem wd_cons_zero {n m : ℕ} (a : Fin m) (w : Fin n → Fin m) :
    wd (Fin.cons a w : Fin (n + 1) → Fin m) 0 = a := by
  unfold wd
  rw [dif_pos (by omega)]
  exact congrArg Fin.val (Fin.cons_zero (α := fun _ => Fin m) a w)

theorem wd_cons_succ {n m : ℕ} (a : Fin m) (w : Fin n → Fin m) (p : ℕ) :
    wd (Fin.cons a w : Fin (n + 1) → Fin m) (p + 1) = wd w p := by
  unfold wd
  by_cases hp : p < n
  · rw [dif_pos (by omega), dif_pos hp]
    exact congrArg Fin.val (Fin.cons_succ (α := fun _ => Fin m) a w ⟨p, hp⟩)
  · rw [dif_neg (by omega), dif_neg hp]

theorem Adm_succ (j : ℕ) (y : ℕ → ℕ) :
    Adm (j + 1) y ↔ (y 0 < y 2 ∧ y 2 ≤ y 1) ∧ Adm j (fun p => y (p + 2)) := by
  have e1 : ∀ i : ℕ, 2 * (i + 1) = 2 * i + 2 := fun i => by ring
  have e2 : ∀ i : ℕ, 2 * (i + 1) + 2 = 2 * i + 2 + 2 := fun i => by ring
  have e3 : ∀ i : ℕ, 2 * (i + 1) + 1 = 2 * i + 1 + 2 := fun i => by ring
  constructor
  · intro h
    refine ⟨by simpa using h 0 (by omega), fun i hi => ?_⟩
    have := h (i + 1) (by omega)
    rw [e2, e3, e1] at this
    exact this
  · rintro ⟨h0, h⟩ i hi
    rcases i with _ | i
    · simpa using h0
    · have := h i (by omega)
      rw [e2, e3, e1]
      exact this

/-- Sums over `Fin (n+1) → Fin m` split off the first letter. -/
theorem sum_cons {n m : ℕ} (f : (Fin (n + 1) → Fin m) → ℕ) :
    ∑ w, f w = ∑ a : Fin m, ∑ w : Fin n → Fin m, f (Fin.cons a w) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.consEquiv fun _ => Fin m) _ _ fun _ => rfl).symm

theorem sum_fin_ite (m v c : ℕ) :
    ∑ a : Fin m, (if (a : ℕ) = v then c else 0) = if v < m then c else 0 := by
  have h1 : ∑ a : Fin m, (if (a : ℕ) = v then c else 0) = ∑ a ∈ range m, (if a = v then c else 0) :=
    Fin.sum_univ_eq_sum_range (fun a => if a = v then c else 0) m
  rw [h1]
  simp only [sum_ite_eq', mem_range]

theorem sum_fin_ge (m c : ℕ) : ∑ b : Fin m, (if c ≤ (b : ℕ) then 1 else 0) = m - c := by
  have h1 : ∑ b : Fin m, (if c ≤ (b : ℕ) then 1 else 0) = ∑ b ∈ range m, (if c ≤ b then 1 else 0) :=
    Fin.sum_univ_eq_sum_range (fun b => if c ≤ b then 1 else 0) m
  rw [h1, ← card_filter]
  convert Nat.card_Ico c m using 2
  ext b
  simp only [mem_filter, mem_range, mem_Ico]
  omega

open Classical in
/-- The indicator of an admissible word with first letter `v`. -/
noncomputable def ind (j m v : ℕ) (w : Fin (2 * j + 1) → Fin m) : ℕ :=
  if Adm j (wd w) ∧ wd w 0 = v then 1 else 0

/-- The number of admissible words with first letter `v`. -/
noncomputable def G (j m v : ℕ) : ℕ := ∑ w, ind j m v w

open Classical in
/-- The number of admissible words. -/
noncomputable def T (j m : ℕ) : ℕ := ∑ w : Fin (2 * j + 1) → Fin m, if Adm j (wd w) then 1 else 0

theorem e_succ_sum (j M : ℕ) : e (j + 1) M = ∑ u ∈ range M, (u + 1) * e j u := by
  induction M with
  | zero => rfl
  | succ M ih => rw [e_succ_succ, ih, sum_range_succ]

theorem sum_tail (j m v : ℕ) (hv : v < m) :
    ∑ c ∈ range m, (if v < c then (m - c) * e j (m - 1 - c) else 0) = e (j + 1) (m - 1 - v) := by
  obtain ⟨M, rfl⟩ : ∃ M, m = v + 1 + M := ⟨m - 1 - v, by omega⟩
  rw [sum_range_add]
  have h0 : ∑ c ∈ range (v + 1),
      (if v < c then (v + 1 + M - c) * e j (v + 1 + M - 1 - c) else 0) = 0 :=
    sum_eq_zero fun c hc => if_neg (by have := mem_range.1 hc; omega)
  rw [h0, zero_add, show v + 1 + M - 1 - v = M by omega, e_succ_sum]
  have hrefl : ∑ x ∈ range M, (M - 1 - x + 1) * e j (M - 1 - x)
      = ∑ x ∈ range M, (x + 1) * e j x :=
    sum_range_reflect (fun x => (x + 1) * e j x) M
  rw [← hrefl]
  refine sum_congr rfl fun x hx => ?_
  have := mem_range.1 hx
  rw [if_pos (show v < v + 1 + x by omega), show v + 1 + M - (v + 1 + x) = M - 1 - x + 1 by omega,
    show v + 1 + M - 1 - (v + 1 + x) = M - 1 - x by omega]

open Classical in
theorem ind_cons (j m v : ℕ) (a b : Fin m) (w : Fin (2 * j + 1) → Fin m) :
    ind (j + 1) m v (Fin.cons a (Fin.cons b w) : Fin (2 * j + 1 + 1 + 1) → Fin m)
      = if (a : ℕ) = v ∧ ((v < wd w 0 ∧ wd w 0 ≤ b) ∧ Adm j (wd w)) then 1 else 0 := by
  unfold ind
  refine if_congr ?_ rfl rfl
  change Adm (j + 1) (wd (Fin.cons a (Fin.cons b w) : Fin (2 * j + 1 + 1 + 1) → Fin m))
      ∧ wd (Fin.cons a (Fin.cons b w) : Fin (2 * j + 1 + 1 + 1) → Fin m) 0 = v ↔ _
  have x0 : wd (Fin.cons a (Fin.cons b w) : Fin (2 * j + 1 + 1 + 1) → Fin m) 0 = a :=
    wd_cons_zero a _
  have x1 : wd (Fin.cons a (Fin.cons b w) : Fin (2 * j + 1 + 1 + 1) → Fin m) 1 = b :=
    (wd_cons_succ a (Fin.cons b w) 0).trans (wd_cons_zero b w)
  have x2 : wd (Fin.cons a (Fin.cons b w) : Fin (2 * j + 1 + 1 + 1) → Fin m) 2 = wd w 0 :=
    (wd_cons_succ a (Fin.cons b w) 1).trans ((wd_cons_succ b w 0).trans rfl)
  have hy : (fun p => wd (Fin.cons a (Fin.cons b w) : Fin (2 * j + 1 + 1 + 1) → Fin m) (p + 2))
      = wd w := by
    funext p
    rw [show p + 2 = (p + 1) + 1 by ring, wd_cons_succ, wd_cons_succ]
  rw [Adm_succ, hy, x0, x1, x2]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    exact ⟨h4, ⟨by omega, h2⟩, h3⟩
  · rintro ⟨h4, ⟨h1, h2⟩, h3⟩
    exact ⟨⟨⟨by omega, h2⟩, h3⟩, h4⟩

/-- **Admissible words with first letter `v`.** -/
theorem G_eq (j m v : ℕ) : G j m v = if v < m then e j (m - 1 - v) else 0 := by
  classical
  induction j generalizing v with
  | zero =>
    unfold G
    change ∑ w : Fin (0 + 1) → Fin m, ind 0 m v w = _
    rw [sum_cons]
    have hA : ∀ a : Fin m, ∑ w : Fin 0 → Fin m, ind 0 m v (Fin.cons a w)
        = if (a : ℕ) = v then 1 else 0 := by
      intro a
      have hw : ∀ w : Fin 0 → Fin m, ind 0 m v (Fin.cons a w) = if (a : ℕ) = v then 1 else 0 := by
        intro w
        unfold ind
        refine if_congr ?_ rfl rfl
        change Adm 0 (wd (Fin.cons a w : Fin (0 + 1) → Fin m))
          ∧ wd (Fin.cons a w : Fin (0 + 1) → Fin m) 0 = v ↔ _
        rw [wd_cons_zero]
        exact ⟨fun h => h.2, fun h => ⟨fun i hi => absurd hi (Nat.not_lt_zero _), h⟩⟩
      rw [sum_congr rfl fun w _ => hw w]
      simp
    rw [sum_congr rfl fun a _ => hA a, sum_fin_ite]
    simp [e]
  | succ j ih =>
    unfold G
    change ∑ w : Fin (2 * j + 1 + 1 + 1) → Fin m, ind (j + 1) m v w = _
    rw [sum_cons]
    have h2 : ∀ a : Fin m, ∑ w' : Fin (2 * j + 1 + 1) → Fin m, ind (j + 1) m v (Fin.cons a w')
        = ∑ b : Fin m, ∑ w : Fin (2 * j + 1) → Fin m,
            ind (j + 1) m v (Fin.cons a (Fin.cons b w)) := fun a =>
      sum_cons (fun w' => ind (j + 1) m v (Fin.cons a w'))
    rw [sum_congr rfl fun a _ => h2 a]
    -- the constraint splits
    set S := ∑ b : Fin m, ∑ w : Fin (2 * j + 1) → Fin m,
      (if (v < wd w 0 ∧ wd w 0 ≤ b) ∧ Adm j (wd w) then 1 else 0) with hS
    have hA : ∀ a : Fin m, ∑ b : Fin m, ∑ w : Fin (2 * j + 1) → Fin m,
        ind (j + 1) m v (Fin.cons a (Fin.cons b w)) = if (a : ℕ) = v then S else 0 := by
      intro a
      by_cases ha : (a : ℕ) = v
      · rw [if_pos ha, hS]
        refine sum_congr rfl fun b _ => sum_congr rfl fun w _ => ?_
        rw [ind_cons]
        simp [ha]
      · rw [if_neg ha]
        refine sum_eq_zero fun b _ => sum_eq_zero fun w _ => ?_
        rw [ind_cons, if_neg fun h => ha h.1]
    rw [sum_congr rfl fun a _ => hA a, sum_fin_ite]
    by_cases hv : v < m
    swap
    · rw [if_neg hv, if_neg hv]
    rw [if_pos hv, if_pos hv, ← sum_tail j m v hv]
    -- `S = ∑_w [v < w₀ ∧ Adm] (m − w₀)`
    have hS1 : S = ∑ w : Fin (2 * j + 1) → Fin m,
        (if v < wd w 0 ∧ Adm j (wd w) then m - wd w 0 else 0) := by
      rw [hS, sum_comm]
      refine sum_congr rfl fun w _ => ?_
      by_cases hw : v < wd w 0 ∧ Adm j (wd w)
      · rw [if_pos hw, ← sum_fin_ge m (wd w 0)]
        refine sum_congr rfl fun b _ => ?_
        by_cases hb : wd w 0 ≤ (b : ℕ)
        · rw [if_pos ⟨⟨hw.1, hb⟩, hw.2⟩, if_pos hb]
        · rw [if_neg fun h => hb h.1.2, if_neg hb]
      · rw [if_neg hw]
        refine sum_eq_zero fun b _ => if_neg fun h => hw ⟨h.1.1, h.2⟩
    -- the right side, through the induction hypothesis
    have hR : ∑ c ∈ range m, (if v < c then (m - c) * e j (m - 1 - c) else 0)
        = ∑ c ∈ range m, ∑ w : Fin (2 * j + 1) → Fin m,
            (if Adm j (wd w) then (if wd w 0 = c then (if v < c then m - c else 0) else 0)
              else 0) := by
      refine sum_congr rfl fun c hc => ?_
      have hcm := mem_range.1 hc
      have hG := ih c
      rw [if_pos hcm] at hG
      by_cases hvc : v < c
      · rw [if_pos hvc, ← hG]
        unfold G
        rw [mul_sum]
        refine sum_congr rfl fun w _ => ?_
        unfold ind
        by_cases h1 : Adm j (wd w) <;> by_cases h2 : wd w 0 = c <;> simp [h1, h2, hvc]
      · rw [if_neg hvc]
        refine (sum_eq_zero fun w _ => ?_).symm
        by_cases h1 : Adm j (wd w) <;> by_cases h2 : wd w 0 = c <;> simp [h1, h2, hvc]
    rw [hS1, hR, sum_comm]
    refine sum_congr rfl fun w _ => ?_
    have hw0 : wd w 0 ∈ range m := mem_range.2 (wd_lt w 0 (by omega))
    by_cases h1 : Adm j (wd w)
    · simp only [h1, and_true, ↓reduceIte, sum_ite_eq, hw0]
    · simp only [h1, and_false, ↓reduceIte, sum_const_zero]

/-- **The number of admissible words** with letters below `m` is `V j m`. -/
theorem T_eq (j m : ℕ) : T j m = V j m := by
  classical
  have hT : T j m = ∑ v ∈ range m, G j m v := by
    unfold T G
    rw [sum_comm]
    refine sum_congr rfl fun w _ => ?_
    have hw0 : wd w 0 ∈ range m := mem_range.2 (wd_lt w 0 (by omega))
    unfold ind
    by_cases h1 : Adm j (wd w)
    · simp only [h1, true_and, ↓reduceIte, sum_ite_eq, hw0]
    · simp only [h1, false_and, ↓reduceIte, sum_const_zero]
  have hG : ∑ v ∈ range m, G j m v = ∑ v ∈ range m, e j (m - 1 - v) :=
    sum_congr rfl fun v hv => by rw [G_eq, if_pos (mem_range.1 hv)]
  rw [hT, hG]
  unfold V
  exact sum_range_reflect (fun u => e j u) m

end Principia.MathDB.P367940
