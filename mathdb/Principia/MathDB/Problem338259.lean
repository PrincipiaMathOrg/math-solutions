import Mathlib

/-!
# MathDB #338259 — nullity equality FAILS for io-decomposable Bell-type Riordan graphs

Write-up: `antoshashakov/Principia-Math-In-Progress`, branch `mathdb-results`,
`mathdb-open-problems/problems/338259/solution.tex`, refuting Conjecture 7.9 of Cheon, Jung,
Kitaev and Mojallal (*Riordan graphs II*, LAA 575 (2019)): every singular io-decomposable Riordan
graph of the Bell type has `η(Aₙ) = η(B)`, where, listing odd vertices first,
`Aₙ ∼ [[A_{⌈n/2⌉}, B], [Bᵀ, 0]]` and `η` is the dimension of the right kernel.

**The objects, for an arbitrary `g ∈ ℤ⟦z⟧`.**  The Bell-type graph `G(g, zg)` has vertices
`1, 2, …`, zero diagonal and, for `i > j`, `a_{ij} = [z^{i−j−1}] g(z)ʲ mod 2` (`adj`).
`IoDecomp g` asks, for EVERY order at once, that even vertices be independent
(`a_{2i,2j} = 0`) and that the odd vertices, relabelled in order, induce the same graph
(`a_{2i−1,2j−1} = a_{ij}`).  `Conj79` quantifies over every `g` with `g(0) = 1` (a proper
Riordan pair), every order `n`, and every singular `Aₙ`.  Asking io-decomposability at all orders
is the strongest hypothesis, so this is the weakest reading of the conjecture.

**The witness (the write-up's).**  `g(z) = ∑ₛ z^{2ˢ−1} E(z^{2ˢ})` with `E = 1 + z⁶ + z⁸ + z¹²`,
encoded by `g(z) = E(z) + z g(z²)`.  Io-decomposability at every order follows from Frobenius:
mod 2, `g(z)² = g(z²)` (`MvPowerSeries.map_frobenius_expand`) and `g = E′(z²) + z g(z²)`.
At `n = 15`, `A₁₅ v = 0` for `v = (1,−1,0,0,1,−1,0,−1,−1,2,0,−1,−1,1,−1)`, so `A₁₅` is singular
and `η(A₁₅) ≥ 1`, while `B` (8 × 7) has an integer left inverse, so `η(B) = 0`.  The entries of
`A₁₅` are read off a table of `[zᵏ] (g mod 2)ʲ`, `j < 15`, `k < 14`, whose every row is checked
against the convolution recurrence by `decide`.  All values were checked in SymPy first
(`η(A₁₅) = 1`, `rank B = 7`, io-decomposability to order 60).
-/

namespace Principia.MathDB.P338259

open PowerSeries

/-! ### The conjecture, for an arbitrary `g` -/

/-- `g mod 2`. -/
noncomputable def red (g : PowerSeries ℤ) : PowerSeries (ZMod 2) :=
  PowerSeries.map (Int.castRingHom (ZMod 2)) g

/-- The Bell-type Riordan graph `G(g, zg)`: `a_{ij} = [z^{i−j−1}] g(z)ʲ mod 2` for `i > j ≥ 1`. -/
noncomputable def adj (g : PowerSeries ℤ) (i j : ℕ) : ZMod 2 := coeff (i - j - 1) (red g ^ j)

/-- The symmetric `0/1` adjacency entry between vertices `i, j ≥ 1`, with zero diagonal. -/
noncomputable def ent (g : PowerSeries ℤ) (i j : ℕ) : ℚ :=
  if j < i then ((adj g i j).val : ℚ) else if i < j then ((adj g j i).val : ℚ) else 0

/-- The adjacency matrix `Aₙ` on vertices `1, …, n`. -/
noncomputable def Amat (g : PowerSeries ℤ) (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  fun a b => ent g ((a : ℕ) + 1) ((b : ℕ) + 1)

/-- The block `B`: rows the odd vertices `1, 3, …`, columns the even vertices `2, 4, …`. -/
noncomputable def Bmat (g : PowerSeries ℤ) (n : ℕ) :
    Matrix (Fin ((n + 1) / 2)) (Fin (n / 2)) ℚ :=
  fun a b => ent g (2 * (a : ℕ) + 1) (2 * (b : ℕ) + 2)

/-- io-decomposability at every order. -/
def IoDecomp (g : PowerSeries ℤ) : Prop :=
  ∀ i j : ℕ, 1 ≤ j → j < i →
    adj g (2 * i) (2 * j) = 0 ∧ adj g (2 * i - 1) (2 * j - 1) = adj g i j

/-- Nullity: the dimension of the right kernel. -/
noncomputable def nullity {m k : Type*} [Fintype m] [Fintype k] (M : Matrix m k ℚ) : ℕ :=
  Module.finrank ℚ (LinearMap.ker M.mulVecLin)

/-- **Conjecture 7.9 of Cheon–Jung–Kitaev–Mojallal.** -/
def Conj79 : Prop :=
  ∀ g : PowerSeries ℤ, constantCoeff g = 1 → IoDecomp g → ∀ n : ℕ,
    (Amat g n).det = 0 → nullity (Amat g n) = nullity (Bmat g n)

/-! ### The witness -/

/-- `E(z) = 1 + z⁶ + z⁸ + z¹²`. -/
def ec (k : ℕ) : ℤ := if k = 0 ∨ k = 6 ∨ k = 8 ∨ k = 12 then 1 else 0

/-- The coefficients of `g = ∑ₛ z^{2ˢ−1} E(z^{2ˢ})`, through `g(z) = E(z) + z g(z²)`. -/
def gc (k : ℕ) : ℤ := ec k + if h : k % 2 = 1 then gc (k / 2) else 0
termination_by k
decreasing_by all_goals first | omega | (simp_wf; omega)

theorem gc_even (k m : ℕ) (h : k = 2 * m) : gc k = ec k := by
  conv_lhs => rw [gc]
  rw [dif_neg (by omega), add_zero]

theorem gc_odd (k m : ℕ) (h : k = 2 * m + 1) : gc k = ec k + gc m := by
  conv_lhs => rw [gc]
  rw [dif_pos (by omega), show k / 2 = m by omega]

/-- The witness series `g`. -/
noncomputable def g : PowerSeries ℤ := PowerSeries.mk gc

theorem coeff_red_g (k : ℕ) : coeff k (red g) = (gc k : ZMod 2) := by
  simp [red, g, coeff_map]

theorem g_const : constantCoeff g = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, g, coeff_mk, gc_even 0 0 rfl]
  decide

/-- `E′(z) = 1 + z³ + z⁴ + z⁶ mod 2`, so that `E(z) = E′(z²)`. -/
noncomputable def E2 : PowerSeries (ZMod 2) :=
  PowerSeries.mk fun k => if k = 0 ∨ k = 3 ∨ k = 4 ∨ k = 6 then 1 else 0

/-- Frobenius in characteristic `2`: `f(z)² = f(z²)`. -/
theorem sq_expand (f : PowerSeries (ZMod 2)) : f ^ 2 = expand 2 two_ne_zero f := by
  have h := MvPowerSeries.map_frobenius_expand (σ := Unit) (R := ZMod 2) 2 two_ne_zero (f := f)
  rw [ZMod.frobenius_zmod, MvPowerSeries.map_id, RingHom.id_apply] at h
  exact h.symm

/-- `g ≡ E′(z²) + z g(z²) (mod 2)`. -/
theorem split : red g = expand 2 two_ne_zero E2 + X * expand 2 two_ne_zero (red g) := by
  ext m
  rw [map_add, coeff_red_g]
  rcases Nat.even_or_odd' m with ⟨k, rfl | rfl⟩
  · rw [coeff_expand_mul, gc_even (2 * k) k rfl]
    rcases k with _ | k
    · simp [E2, ec]
    · rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, coeff_succ_X_mul,
        coeff_expand_of_not_dvd 2 two_ne_zero (red g) (m := 2 * k + 1) (by omega), add_zero,
        show 2 * k + 1 + 1 = 2 * (k + 1) by ring]
      rw [ec, E2, coeff_mk]
      by_cases hk : k + 1 = 3 ∨ k + 1 = 4 ∨ k + 1 = 6
      · rw [if_pos (show 2 * (k + 1) = 0 ∨ 2 * (k + 1) = 6 ∨ 2 * (k + 1) = 8 ∨
            2 * (k + 1) = 12 by omega),
          if_pos (show k + 1 = 0 ∨ k + 1 = 3 ∨ k + 1 = 4 ∨ k + 1 = 6 by omega)]
        simp
      · rw [if_neg (show ¬(2 * (k + 1) = 0 ∨ 2 * (k + 1) = 6 ∨ 2 * (k + 1) = 8 ∨
            2 * (k + 1) = 12) by omega),
          if_neg (show ¬(k + 1 = 0 ∨ k + 1 = 3 ∨ k + 1 = 4 ∨ k + 1 = 6) by omega)]
        simp
  · rw [coeff_expand_of_not_dvd 2 two_ne_zero E2 (m := 2 * k + 1) (by omega), zero_add,
      coeff_succ_X_mul, coeff_expand_mul, coeff_red_g, gc_odd (2 * k + 1) k rfl]
    have h0 : ec (2 * k + 1) = 0 := by
      rw [ec, if_neg (show ¬(2 * k + 1 = 0 ∨ 2 * k + 1 = 6 ∨ 2 * k + 1 = 8 ∨
        2 * k + 1 = 12) by omega)]
    rw [h0]
    simp

theorem key_odd (h : PowerSeries (ZMod 2)) (m : ℕ) :
    coeff (2 * m + 1) (expand 2 two_ne_zero h * red g) = coeff m (h * red g) := by
  conv_lhs => rw [split]
  rw [mul_add, ← map_mul, map_add,
    coeff_expand_of_not_dvd 2 two_ne_zero (h * E2) (m := 2 * m + 1) (by omega), zero_add,
    mul_left_comm, ← map_mul, coeff_succ_X_mul, coeff_expand_mul]

/-- **The witness is io-decomposable at every order.** -/
theorem io : IoDecomp g := by
  intro i j hj hij
  constructor
  · unfold adj
    rw [pow_mul, sq_expand, ← map_pow,
      coeff_expand_of_not_dvd 2 two_ne_zero _ (m := 2 * i - 2 * j - 1) (by omega)]
  · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    obtain ⟨m, rfl⟩ : ∃ m, i = j' + 1 + m + 1 := ⟨i - j' - 2, by omega⟩
    unfold adj
    rw [show 2 * (j' + 1 + m + 1) - 1 - (2 * (j' + 1) - 1) - 1 = 2 * m + 1 by omega,
      show j' + 1 + m + 1 - (j' + 1) - 1 = m by omega,
      show 2 * (j' + 1) - 1 = 2 * j' + 1 by omega,
      pow_succ, pow_mul, sq_expand, ← map_pow, key_odd, ← pow_succ]

/-- `gc 0, …, gc 13`, unfolded through the defining recursion. -/
theorem gc_small : gc 0 = 1 ∧ gc 1 = 1 ∧ gc 2 = 0 ∧
    gc 3 = 1 ∧ gc 4 = 0 ∧ gc 5 = 0 ∧ gc 6 = 1 ∧ gc 7 = 1 ∧ gc 8 = 1 ∧ gc 9 = 0 ∧ gc 10 = 0 ∧
    gc 11 = 0 ∧ gc 12 = 1 ∧ gc 13 = 1 := by
  have h0 : gc 0 = 1 := by rw [gc_even 0 0 rfl]; decide
  have h1 : gc 1 = 1 := by rw [gc_odd 1 0 rfl, h0]; decide
  have h2 : gc 2 = 0 := by rw [gc_even 2 1 rfl]; decide
  have h3 : gc 3 = 1 := by rw [gc_odd 3 1 rfl, h1]; decide
  have h4 : gc 4 = 0 := by rw [gc_even 4 2 rfl]; decide
  have h5 : gc 5 = 0 := by rw [gc_odd 5 2 rfl, h2]; decide
  have h6 : gc 6 = 1 := by rw [gc_even 6 3 rfl]; decide
  have h7 : gc 7 = 1 := by rw [gc_odd 7 3 rfl, h3]; decide
  have h8 : gc 8 = 1 := by rw [gc_even 8 4 rfl]; decide
  have h9 : gc 9 = 0 := by rw [gc_odd 9 4 rfl, h4]; decide
  have h10 : gc 10 = 0 := by rw [gc_even 10 5 rfl]; decide
  have h11 : gc 11 = 0 := by rw [gc_odd 11 5 rfl, h5]; decide
  have h12 : gc 12 = 1 := by rw [gc_even 12 6 rfl]; decide
  have h13 : gc 13 = 1 := by rw [gc_odd 13 6 rfl, h6]; decide
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

/-- The coefficients of `g mod 2` below `z¹⁴`. -/
def GLc : List (ZMod 2) := [1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 1, 1]

/-- `Tl[j][k] = [zᵏ] (g mod 2)ʲ` for `j < 15`, `k < 14` (generated, then checked by `step_T`). -/
def Tl : List (List (ZMod 2)) := [
  [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 1, 1],
  [1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0],
  [1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 1],
  [1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0],
  [1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0],
  [1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0],
  [1, 1, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0],
  [1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
  [1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 1, 1],
  [1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0],
  [1, 1, 1, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0],
  [1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0],
  [1, 1, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1],
  [1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0]]

/-- The literal left inverse of `B`: rows `2..8` of `B` form a unimodular `7 × 7` block. -/
def XL : Matrix (Fin 7) (Fin 8) ℚ :=
  !![0, -1, 1, 0, 0, 0, -1, 1;
    0, 1, 0, 0, 0, -1, 1, -1;
    0, 0, 0, 0, 0, 1, -1, 0;
    0, 0, 0, 1, 0, -1, 0, 0;
    0, 0, -1, -1, 1, 1, 1, 0;
    0, -1, 2, 1, -1, -1, -1, 0;
    0, 1, -1, 0, 0, 0, 1, 0]

/-- `T j k = Tl[j][k]`. -/
def T (j k : ℕ) : ZMod 2 := (Tl.getD j []).getD k 0

/-- Every row of the table is the convolution of `GLc` with the previous row. -/
theorem step_T : ∀ j < 14, ∀ k < 14,
    (∑ i ∈ Finset.range (k + 1), GLc.getD i 0 * T j (k - i)) = T (j + 1) k := by
  decide +kernel

theorem coeff_red_small (i : ℕ) (hi : i < 14) : coeff i (red g) = GLc.getD i 0 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := gc_small
  rw [coeff_red_g]
  interval_cases i <;>
    simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13] <;> decide

/-- `[zᵏ] (g mod 2)ʲ = T j k` for `j < 15`, `k < 14`. -/
theorem coeff_pow_T : ∀ j, j < 15 → ∀ k, k < 14 → coeff k (red g ^ j) = T j k := by
  intro j
  induction j with
  | zero =>
    intro _ k hk
    rw [pow_zero, coeff_one]
    interval_cases k <;> decide
  | succ j ih =>
    intro hj k hk
    rw [pow_succ', coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      ← step_T j (by omega) k hk]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    dsimp only
    rw [coeff_red_small i (by omega), ih (by omega) (k - i) (by omega)]

/-- The adjacency entry computed from the table. -/
def entT (i j : ℕ) : ℚ :=
  if j < i then ((T j (i - j - 1)).val : ℚ) else if i < j then ((T i (j - i - 1)).val : ℚ) else 0

theorem ent_eq (i j : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ 15) (hj1 : 1 ≤ j) (hj : j ≤ 15) :
    ent g i j = entT i j := by
  unfold ent entT adj
  split_ifs with h1 h2
  · rw [coeff_pow_T j (by omega) (i - j - 1) (by omega)]
  · rw [coeff_pow_T i (by omega) (j - i - 1) (by omega)]
  · rfl

/-- `A₁₅`, from the table. -/
def MA : Matrix (Fin 15) (Fin 15) ℚ := fun a b => entT ((a : ℕ) + 1) ((b : ℕ) + 1)

/-- `B` for `n = 15`, from the table. -/
def MB : Matrix (Fin 8) (Fin 7) ℚ := fun a b => entT (2 * (a : ℕ) + 1) (2 * (b : ℕ) + 2)

theorem Amat_eq : Amat g 15 = MA := by
  funext a b
  have ha := a.isLt
  have hb := b.isLt
  exact ent_eq _ _ (by omega) (by omega) (by omega) (by omega)

theorem Bmat_eq : Bmat g 15 = MB := by
  funext a b
  have ha : (a : ℕ) < 8 := a.isLt
  have hb : (b : ℕ) < 7 := b.isLt
  exact ent_eq _ _ (by omega) (by omega) (by omega) (by omega)

/-- The write-up's kernel vector of `A₁₅`, in the original vertex order. -/
def v : Fin 15 → ℚ := ![1, -1, 0, 0, 1, -1, 0, -1, -1, 2, 0, -1, -1, 1, -1]

theorem MA_v : Matrix.mulVec MA v = 0 := by decide +kernel

theorem XL_MB : XL * MB = 1 := by decide +kernel

/-- **MathDB #338259: Conjecture 7.9 is false** — at `n = 15`, `η(A₁₅) ≥ 1` but `η(B) = 0`. -/
theorem not_conj79 : ¬ Conj79 := by
  intro h
  have hv0 : v ≠ 0 := fun hv => by
    have := congrFun hv 0
    norm_num [v] at this
  have hA : Matrix.mulVec (Amat g 15) v = 0 := by
    rw [Amat_eq]
    exact MA_v
  have hdet : (Amat g 15).det = 0 := Matrix.exists_mulVec_eq_zero_iff.1 ⟨v, hv0, hA⟩
  have heq := h g g_const io 15 hdet
  have hpos : 0 < nullity (Amat g 15) := by
    unfold nullity
    rw [Module.finrank_pos_iff_exists_ne_zero]
    refine ⟨⟨v, ?_⟩, fun h0 => hv0 (congrArg Subtype.val h0)⟩
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
    exact hA
  have hzero : nullity (Bmat g 15) = 0 := by
    unfold nullity
    have hker : LinearMap.ker (Bmat g 15).mulVecLin = ⊥ := by
      rw [LinearMap.ker_eq_bot']
      intro x hx
      rw [Matrix.mulVecLin_apply, Bmat_eq] at hx
      have h2 := congrArg (fun y => Matrix.mulVec XL y) hx
      simpa [Matrix.mulVec_mulVec, XL_MB] using h2
    rw [hker]
    simp
  omega

end Principia.MathDB.P338259
