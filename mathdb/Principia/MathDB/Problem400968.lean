import Mathlib

/-!
# MathDB #400968 — non-completable partial probability tables need not form a convex set

Write-up: `antoshashakov/Principia-Math-In-Progress`, branch `mathdb-results`,
`mathdb-open-problems/problems/400968/solution.tex`, answering the question in Kummer's Oberwolfach
report (p. 1271): for an observed pattern `E` with full-dimensional completion image and
`|E| = ∑ᵢ (dᵢ − 1)`, is the set of nonnegative partial tensors with no completion to the joint
distribution of independent random variables convex?

**What is refuted.**  `KummerConj` is the question's positive answer for `3 × 3` tables only (a
restriction), with the extra hypotheses that `E` observes every row and column.  A partial table
is `p : E → ℝ`; it is completable when `p (i, j) = aᵢ bⱼ` on `E` for probability vectors `a, b`.
"Full-dimensional" is `(interior (CompImage E)).Nonempty`.

**The witness (the write-up's).**  `E = {(0,0), (0,1), (1,0), (2,2)}`, `P = (1/32, 1/8, 1/8, 1/16)`,
`Q = (15/32, 1/8, 1/8, 1/16)`.  A completion of `(x, y, z, w)` forces
`(a₀+a₁)(b₀+b₁) = x + y + z + yz/x` and `(1−a₀−a₁)(1−b₀−b₁) = w`, and with `w = 1/16` these force
the first product `≤ 9/16` (`core`); `P` and `Q` give `25/32` and `361/480`, so neither completes
(`not_completable`).  Their midpoint `(1/4, 1/8, 1/8, 1/16)` completes with
`a = b = (1/2, 1/4, 1/4)`.  The write-up's inverse-function-theorem step for full-dimensionality is
replaced by an explicit intermediate-value construction (`solve`): every point within `10⁻⁵` of
`(1/6, 1/6, 1/12, 1/12)` in each coordinate has a completion.  All values were checked in exact
rational arithmetic.

**Absent:** Task 2 onward (the classification of convex patterns).
-/

namespace Principia.MathDB.P400968

open Finset Set

attribute [local simp] Matrix.cons_val_two Matrix.tail_cons

/-- Cells of a `3 × 3` table. -/
abbrev Cell := Fin 3 × Fin 3

/-- A probability vector. -/
def IsProb (a : Fin 3 → ℝ) : Prop := (∀ i, 0 ≤ a i) ∧ ∑ i, a i = 1

/-- `p` is the restriction to `E` of the joint table of independent `a, b`. -/
def Completable (E : Finset Cell) (p : E → ℝ) : Prop :=
  ∃ a b : Fin 3 → ℝ, IsProb a ∧ IsProb b ∧ ∀ e : E, p e = a e.1.1 * b e.1.2

/-- The completion image. -/
def CompImage (E : Finset Cell) : Set (E → ℝ) := {p | Completable E p}

/-- Nonnegative non-completable partial tables. -/
def NonCompl (E : Finset Cell) : Set (E → ℝ) := {p | (∀ e, 0 ≤ p e) ∧ ¬ Completable E p}

/-- The question's positive answer, for `3 × 3` tables. -/
def KummerConj : Prop :=
  ∀ E : Finset Cell, E.card = 4 → (∀ i, ∃ j, (i, j) ∈ E) → (∀ j, ∃ i, (i, j) ∈ E) →
    (interior (CompImage E)).Nonempty → Convex ℝ (NonCompl E)

/-- The pattern `{(0,0), (0,1), (1,0), (2,2)}`. -/
def E : Finset Cell := {(0, 0), (0, 1), (1, 0), (2, 2)}

def e00 : E := ⟨(0, 0), by decide⟩
def e01 : E := ⟨(0, 1), by decide⟩
def e10 : E := ⟨(1, 0), by decide⟩
def e22 : E := ⟨(2, 2), by decide⟩

theorem E_cases (e : E) : e = e00 ∨ e = e01 ∨ e = e10 ∨ e = e22 := by
  obtain ⟨c, hc⟩ := e
  simp only [E, Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr rfl))

/-- The square-root inequality `√S + √w ≤ 1` at `w = 1/16`, without square roots. -/
theorem core (α β : ℝ) (hα : α ≤ 1) (hβ : β ≤ 1) (hS : 9 / 16 < α * β)
    (hw : (1 - α) * (1 - β) = 1 / 16) : False := by
  have h1 : 3 / 2 < α + β := by nlinarith
  have h2 : α + β < 5 / 2 := by linarith
  nlinarith [sq_nonneg (α - β), mul_pos (sub_pos.2 h1) (sub_pos.2 h2)]

theorem not_completable (p : E → ℝ) (hx : 0 < p e00) (hw : p e22 = 1 / 16)
    (hS : 9 / 16 < p e00 + p e01 + p e10 + p e01 * p e10 / p e00) : ¬ Completable E p := by
  rintro ⟨a, b, ⟨ha0, ha1⟩, ⟨hb0, hb1⟩, h⟩
  have h00 : p e00 = a 0 * b 0 := h e00
  have h01 : p e01 = a 0 * b 1 := h e01
  have h10 : p e10 = a 1 * b 0 := h e10
  have h22 : p e22 = a 2 * b 2 := h e22
  rw [Fin.sum_univ_three] at ha1 hb1
  have hk : p e01 * p e10 / p e00 = a 1 * b 1 := by
    rw [div_eq_iff hx.ne', h00, h01, h10]
    ring
  rw [hk, h00, h01, h10] at hS
  have hS2 : 9 / 16 < (a 0 + a 1) * (b 0 + b 1) := by nlinarith
  have hw2 : (1 - (a 0 + a 1)) * (1 - (b 0 + b 1)) = 1 / 16 := by
    rw [← hw, h22, show a 2 = 1 - (a 0 + a 1) by linarith, show b 2 = 1 - (b 0 + b 1) by linarith]
  exact core _ _ (by linarith [ha0 2]) (by linarith [hb0 2]) hS2 hw2

/-- Every point within `10⁻⁵` of `(1/6, 1/6, 1/12, 1/12)` has a completion. -/
theorem solve (x y z w : ℝ) (hx1 : 1 / 6 - 1 / 100000 < x) (hx2 : x < 1 / 6 + 1 / 100000)
    (hy1 : 1 / 6 - 1 / 100000 < y) (hy2 : y < 1 / 6 + 1 / 100000)
    (hz1 : 1 / 12 - 1 / 100000 < z) (hz2 : z < 1 / 12 + 1 / 100000)
    (hw1 : 1 / 12 - 1 / 100000 < w) (hw2 : w < 1 / 12 + 1 / 100000) :
    ∃ a b : Fin 3 → ℝ, IsProb a ∧ IsProb b ∧
      a 0 * b 0 = x ∧ a 0 * b 1 = y ∧ a 1 * b 0 = z ∧ a 2 * b 2 = w := by
  have hx : 0 < x := by linarith
  have hcont : ContinuousOn (fun s : ℝ => (1 - s * (x + z) / x) * (1 - (x + y) / s))
      (Icc (47 / 100) (53 / 100)) := by
    apply ContinuousOn.mul
    · exact continuousOn_const.sub ((continuousOn_id.mul continuousOn_const).div_const x)
    · exact continuousOn_const.sub (continuousOn_const.div continuousOn_id
        fun s hs => ne_of_gt (by linarith [hs.1]))
  -- the value at `47/100` is at least `w`
  have hA1 : 2948 / 10000 ≤ 1 - 47 / 100 * (x + z) / x := by
    have : 47 / 100 * (x + z) / x ≤ 7052 / 10000 := by
      rw [div_le_iff₀ hx]
      nlinarith
    linarith
  have hA2 : 2906 / 10000 ≤ 1 - (x + y) / (47 / 100) := by
    have : (x + y) / (47 / 100) ≤ 7094 / 10000 := by
      rw [div_le_iff₀ (by norm_num)]
      linarith
    linarith
  have hf1 : w ≤ (1 - 47 / 100 * (x + z) / x) * (1 - (x + y) / (47 / 100)) := by
    nlinarith [mul_le_mul hA1 hA2 (by norm_num) (by linarith)]
  -- the value at `53/100` is at most `w`
  have hB1 : 1 - 53 / 100 * (x + z) / x ≤ 206 / 1000 := by
    have : 794 / 1000 ≤ 53 / 100 * (x + z) / x := by
      rw [le_div_iff₀ hx]
      nlinarith
    linarith
  have hB1' : 0 ≤ 1 - 53 / 100 * (x + z) / x := by
    have : 53 / 100 * (x + z) / x ≤ 1 := by
      rw [div_le_iff₀ hx]
      nlinarith
    linarith
  have hB2 : 1 - (x + y) / (53 / 100) ≤ 3712 / 10000 := by
    have : 6288 / 10000 ≤ (x + y) / (53 / 100) := by
      rw [le_div_iff₀ (by norm_num)]
      linarith
    linarith
  have hB2' : 0 ≤ 1 - (x + y) / (53 / 100) := by
    have : (x + y) / (53 / 100) ≤ 1 := by
      rw [div_le_iff₀ (by norm_num)]
      linarith
    linarith
  have hf2 : (1 - 53 / 100 * (x + z) / x) * (1 - (x + y) / (53 / 100)) ≤ w := by
    nlinarith [mul_le_mul hB1 hB2 hB2' (by norm_num)]
  obtain ⟨s, hs, hfs⟩ := intermediate_value_Icc' (by norm_num) hcont ⟨hf2, hf1⟩
  have hfs' : (1 - s * (x + z) / x) * (1 - (x + y) / s) = w := hfs
  have hs0 : 0 < s := by linarith [hs.1]
  have hsne : s ≠ 0 := hs0.ne'
  have hxne : x ≠ 0 := hx.ne'
  have hsz : s * z / x ≤ 3 / 10 := by
    rw [div_le_iff₀ hx]
    nlinarith [hs.2]
  have hxy : (x + y) / s ≤ 1 := by
    rw [div_le_iff₀ hs0]
    linarith [hs.1]
  refine ⟨![s, s * z / x, 1 - s - s * z / x], ![x / s, y / s, 1 - x / s - y / s],
    ⟨fun i => ?_, ?_⟩, ⟨fun i => ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · fin_cases i
    · exact hs0.le
    · exact div_nonneg (mul_nonneg hs0.le (by linarith)) hx.le
    · show 0 ≤ 1 - s - s * z / x
      linarith [hs.2]
  · rw [Fin.sum_univ_three]
    show s + s * z / x + (1 - s - s * z / x) = 1
    ring
  · fin_cases i
    · exact div_nonneg hx.le hs0.le
    · exact div_nonneg (by linarith) hs0.le
    · show 0 ≤ 1 - x / s - y / s
      have : x / s + y / s = (x + y) / s := by ring
      linarith
  · rw [Fin.sum_univ_three]
    show x / s + y / s + (1 - x / s - y / s) = 1
    ring
  · show s * (x / s) = x
    field_simp
  · show s * (y / s) = y
    field_simp
  · show s * z / x * (x / s) = z
    field_simp
  · show (1 - s - s * z / x) * (1 - x / s - y / s) = w
    rw [← hfs']
    field_simp
    ring

/-- The table behind `P` (entries off `E` are irrelevant). -/
noncomputable def tabP : Fin 3 → Fin 3 → ℝ :=
  ![![1 / 32, 1 / 8, 0], ![1 / 8, 0, 0], ![0, 0, 1 / 16]]

/-- The table behind `Q`. -/
noncomputable def tabQ : Fin 3 → Fin 3 → ℝ :=
  ![![15 / 32, 1 / 8, 0], ![1 / 8, 0, 0], ![0, 0, 1 / 16]]

/-- The table behind the center `u0`. -/
noncomputable def tabU : Fin 3 → Fin 3 → ℝ :=
  ![![1 / 6, 1 / 6, 0], ![1 / 12, 0, 0], ![0, 0, 1 / 12]]

/-- `P = (1/32, 1/8, 1/8, 1/16)` on `E`. -/
noncomputable def P : E → ℝ := fun e => tabP e.1.1 e.1.2

/-- `Q = (15/32, 1/8, 1/8, 1/16)` on `E`. -/
noncomputable def Q : E → ℝ := fun e => tabQ e.1.1 e.1.2

/-- The center of the box, `(1/6, 1/6, 1/12, 1/12)`. -/
noncomputable def u0 : E → ℝ := fun e => tabU e.1.1 e.1.2

theorem P_mem : P ∈ NonCompl E := by
  refine ⟨fun e => ?_, not_completable P ?_ ?_ ?_⟩
  · rcases E_cases e with rfl | rfl | rfl | rfl <;> norm_num [P, tabP, e00, e01, e10, e22]
  · norm_num [P, tabP, e00]
  · norm_num [P, tabP, e22]
  · norm_num [P, tabP, e00, e01, e10]

theorem Q_mem : Q ∈ NonCompl E := by
  refine ⟨fun e => ?_, not_completable Q ?_ ?_ ?_⟩
  · rcases E_cases e with rfl | rfl | rfl | rfl <;> norm_num [Q, tabQ, e00, e01, e10, e22]
  · norm_num [Q, tabQ, e00]
  · norm_num [Q, tabQ, e22]
  · norm_num [Q, tabQ, e00, e01, e10]

theorem mid_completable : Completable E ((1 / 2 : ℝ) • P + (1 / 2 : ℝ) • Q) := by
  refine ⟨![1 / 2, 1 / 4, 1 / 4], ![1 / 2, 1 / 4, 1 / 4], ⟨fun i => ?_, ?_⟩, ⟨fun i => ?_, ?_⟩,
    fun e => ?_⟩
  · fin_cases i <;> norm_num
  · norm_num [Fin.sum_univ_three]
  · fin_cases i <;> norm_num
  · norm_num [Fin.sum_univ_three]
  · rcases E_cases e with rfl | rfl | rfl | rfl <;> norm_num [P, Q, tabP, tabQ, e00, e01, e10, e22]

theorem full_dim : (interior (CompImage E)).Nonempty := by
  refine ⟨u0, mem_interior_iff_mem_nhds.2 (Metric.mem_nhds_iff.2 ⟨1 / 100000, by norm_num,
    fun p hp => ?_⟩)⟩
  rw [Metric.mem_ball, dist_pi_lt_iff (by norm_num)] at hp
  have hb : ∀ e : E, u0 e - 1 / 100000 < p e ∧ p e < u0 e + 1 / 100000 := fun e => by
    have := hp e
    rw [Real.dist_eq, abs_lt] at this
    constructor <;> linarith [this.1, this.2]
  have h00 := hb e00
  have h01 := hb e01
  have h10 := hb e10
  have h22 := hb e22
  rw [show u0 e00 = 1 / 6 by norm_num [u0, tabU, e00]] at h00
  rw [show u0 e01 = 1 / 6 by norm_num [u0, tabU, e01]] at h01
  rw [show u0 e10 = 1 / 12 by norm_num [u0, tabU, e10]] at h10
  rw [show u0 e22 = 1 / 12 by norm_num [u0, tabU, e22]] at h22
  obtain ⟨a, b, ha, hb', h1, h2, h3, h4⟩ :=
    solve (p e00) (p e01) (p e10) (p e22) (by linarith [h00.1]) (by linarith [h00.2])
      (by linarith [h01.1]) (by linarith [h01.2]) (by linarith [h10.1]) (by linarith [h10.2])
      (by linarith [h22.1]) (by linarith [h22.2])
  refine ⟨a, b, ha, hb', fun e => ?_⟩
  rcases E_cases e with rfl | rfl | rfl | rfl
  · exact h1.symm
  · exact h2.symm
  · exact h3.symm
  · exact h4.symm

/-- **MathDB #400968: the non-completable partial tables need not be convex.** -/
theorem not_kummerConj : ¬ KummerConj := by
  intro h
  have hc := h E (by decide) (by decide) (by decide) full_dim
  have hmid : (1 / 2 : ℝ) • P + (1 / 2 : ℝ) • Q ∈ NonCompl E :=
    hc P_mem Q_mem (by norm_num) (by norm_num) (by norm_num)
  exact hmid.2 mid_completable

end Principia.MathDB.P400968
