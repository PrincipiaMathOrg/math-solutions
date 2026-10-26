import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic

/-!
# MathDB #354788 — the four q-Stirling families are bottom heavy (Sagan–Swanson Conj. 7.6)

Write-up: `antoshashakov/Principia-Math-In-Progress`, branch `mathdb-results`,
`mathdb-open-problems/problems/354788/solution.tex`, proving Conjecture 7.6 of Sagan and Swanson.

**The objects, exactly as in the source.**  `[m]_q = 1 + q + ⋯ + q^{m−1}` (`[0]_q = 0`), and the
four families with `S[0,k] = c[0,k] = S_B[0,k] = c_B[0,k] = δ_{0k}` and, for `n ≥ 1`,
`S[n,k] = S[n−1,k−1] + [k] S[n−1,k]`, `c[n,k] = c[n−1,k−1] + [n−1] c[n−1,k]`,
`S_B[n,k] = S_B[n−1,k−1] + [2k+1] S_B[n−1,k]`, `c_B[n,k] = c_B[n−1,k−1] + [2n−1] c_B[n−1,k]`
(the source's equations (2), (7), (12), (14)), entries outside `0 ≤ k ≤ n` being zero.  A
polynomial of degree `D` is **bottom heavy** when `a_i ≥ a_{D−i}` for `0 ≤ i < D/2`; constants and
`0` qualify vacuously.  `BottomHeavy` below is that, with `D = natDegree`.  The polynomials have
natural-number coefficients, so they live in `ℕ[X]`.

**The proof, as in the write-up.**
1. *Products of q-integers are symmetric and unimodal.*  Stated without a half-integer center as
   `DU p d`: on the `ℤ`-extended coefficient sequence, `|2x − d| ≤ |2y − d|` forces `p_y ≤ p_x`.
   `DU_qmul` shows multiplication by `[m]_q` (`m ≥ 1`) preserves it with `d ↦ d + m − 1`, through
   symmetry and the step `g_x − g_{x−1} = p_x − p_{x−m}`.
2. *Nonnegative sums of such are bottom heavy*, each summand compared at its own center via
   `(2(D−i) − d)² − (2i − d)² = 4(D − 2i)(D − d) ≥ 0`.
3. *Every entry of every family is such a sum* (`InC`), by induction on `n`: the class is closed
   under addition and under multiplication by any `[m]_q`, and every recurrence coefficient is one.
The stronger statement — every finite sum of products of q-integers is bottom heavy — is
`sumQ_bottomHeavy`.  Checked in Python (all four families to `n = 9`, and closure of `DU` under
`[m]_q` exhaustively on small sequences) before this file was written.
-/

namespace Principia.MathDB.P354788

open Polynomial Finset

/-- The q-integer `[m]_q = 1 + q + ⋯ + q^{m−1}`. -/
noncomputable def qint (m : ℕ) : ℕ[X] := ∑ i ∈ range m, X ^ i

/-- Sagan–Swanson's `S[n,k]` (their eq. (2)). -/
noncomputable def S : ℕ → ℕ → ℕ[X]
  | 0, k => if k = 0 then 1 else 0
  | n + 1, 0 => qint 0 * S n 0
  | n + 1, k + 1 => S n k + qint (k + 1) * S n (k + 1)

/-- Sagan–Swanson's `c[n,k]` (their eq. (7)). -/
noncomputable def c : ℕ → ℕ → ℕ[X]
  | 0, k => if k = 0 then 1 else 0
  | n + 1, 0 => qint n * c n 0
  | n + 1, k + 1 => c n k + qint n * c n (k + 1)

/-- Sagan–Swanson's `S_B[n,k]` (their eq. (12)). -/
noncomputable def SB : ℕ → ℕ → ℕ[X]
  | 0, k => if k = 0 then 1 else 0
  | n + 1, 0 => qint 1 * SB n 0
  | n + 1, k + 1 => SB n k + qint (2 * (k + 1) + 1) * SB n (k + 1)

/-- Sagan–Swanson's `c_B[n,k]` (their eq. (14)); `[2n − 1]` at row `n + 1` is `[2n + 1]`. -/
noncomputable def cB : ℕ → ℕ → ℕ[X]
  | 0, k => if k = 0 then 1 else 0
  | n + 1, 0 => qint (2 * n + 1) * cB n 0
  | n + 1, k + 1 => cB n k + qint (2 * n + 1) * cB n (k + 1)

/-- Bottom heaviness: `a_{D−i} ≤ a_i` for `2i < D`, `D` the degree. -/
def BottomHeavy (F : ℕ[X]) : Prop :=
  ∀ i, 2 * i < F.natDegree → F.coeff (F.natDegree - i) ≤ F.coeff i

/-! ### The `ℤ`-extended coefficient sequence and the symmetric-unimodal invariant -/

/-- Coefficients extended by zero to negative indices. -/
noncomputable def ext (p : ℕ[X]) (x : ℤ) : ℕ := if x < 0 then 0 else p.coeff x.toNat

theorem ext_nat (p : ℕ[X]) (n : ℕ) : ext p n = p.coeff n := by
  simp [ext]

theorem ext_neg (p : ℕ[X]) {x : ℤ} (h : x < 0) : ext p x = 0 := by
  simp [ext, h]

/-- Symmetric and unimodal about `d/2`: coefficients do not increase with distance from center. -/
def DU (p : ℕ[X]) (d : ℤ) : Prop :=
  ∀ x y : ℤ, |2 * x - d| ≤ |2 * y - d| → ext p y ≤ ext p x

theorem DU.symm {p : ℕ[X]} {d : ℤ} (h : DU p d) (x : ℤ) : ext p (d - x) = ext p x := by
  apply le_antisymm
  · exact h x (d - x) (le_of_eq (by rw [show 2 * (d - x) - d = -(2 * x - d) by ring, abs_neg]))
  · exact h (d - x) x (le_of_eq (by rw [show 2 * (d - x) - d = -(2 * x - d) by ring, abs_neg]))

theorem qint_zero : qint 0 = 0 := by
  simp [qint]

theorem qint_coeff_zero {m : ℕ} (hm : 1 ≤ m) : (qint m).coeff 0 = 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [qint, Finset.sum_range_succ', coeff_add, finsetSum_coeff]
  simp [coeff_X_pow]

/-- `(qint m * p)_x = ∑_{t<m} p_{x−t}`. -/
theorem ext_qmul (m : ℕ) (p : ℕ[X]) (x : ℤ) :
    ext (qint m * p) x = ∑ t ∈ range m, ext p (x - t) := by
  by_cases hx : x < 0
  · rw [ext_neg _ hx]
    symm
    apply Finset.sum_eq_zero
    intro t _
    exact ext_neg _ (by omega)
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, x = n := ⟨x.toNat, by omega⟩
    rw [ext_nat, qint, Finset.sum_mul, finsetSum_coeff]
    apply Finset.sum_congr rfl
    intro t _
    rw [coeff_X_pow_mul']
    split_ifs with h
    · rw [show ((n : ℤ) - t) = ((n - t : ℕ) : ℤ) by omega, ext_nat]
    · rw [ext_neg _ (by omega)]

theorem DU_one : DU 1 0 := by
  intro x y hxy
  by_cases hy : y = 0
  · subst hy
    have h3 : |2 * (0 : ℤ) - 0| = 0 := by norm_num
    rw [h3] at hxy
    have h4 : |2 * x - 0| = 0 := le_antisymm hxy (abs_nonneg _)
    rw [abs_eq_zero] at h4
    have hx0 : x = 0 := by omega
    rw [hx0]
  · have h0 : ext 1 y = 0 := by
      unfold ext
      split_ifs with h
      · rfl
      · rw [coeff_one, if_neg (by omega)]
    rw [h0]
    exact Nat.zero_le _

/-- **Multiplication by a q-integer preserves the invariant**, shifting the center. -/
theorem DU_qmul {p : ℕ[X]} {d : ℤ} (h : DU p d) {m : ℕ} (hm : 1 ≤ m) :
    DU (qint m * p) (d + m - 1) := by
  have gsym : ∀ x, ext (qint m * p) (d + m - 1 - x) = ext (qint m * p) x := by
    intro x
    rw [ext_qmul, ext_qmul, ← Finset.sum_range_reflect (fun t : ℕ => ext p (x - t)) m]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' := Finset.mem_range.mp hj
    rw [show d + m - 1 - x - (j : ℤ) = d - (x - ((m - 1 - j : ℕ) : ℤ)) by omega]
    exact h.symm _
  have gstep : ∀ x : ℤ, 2 * x ≤ d + m → ext (qint m * p) (x - 1) ≤ ext (qint m * p) x := by
    intro x hx
    have hsum : ext (qint m * p) x + ext p (x - m) = ext (qint m * p) (x - 1) + ext p x := by
      rw [ext_qmul, ext_qmul]
      have a := Finset.sum_range_succ (fun t : ℕ => ext p (x - t)) m
      have b := Finset.sum_range_succ' (fun t : ℕ => ext p (x - t)) m
      have cc : ∑ t ∈ range m, ext p (x - ((t + 1 : ℕ) : ℤ)) =
          ∑ t ∈ range m, ext p (x - 1 - t) := by
        apply Finset.sum_congr rfl
        intro t _
        congr 1
        push_cast
        ring
      simp only [Nat.cast_zero, sub_zero] at a b
      rw [cc] at b
      omega
    have hle : ext p (x - m) ≤ ext p x := by
      apply h x (x - m)
      rw [← sq_le_sq]
      nlinarith [mul_nonneg (show (0 : ℤ) ≤ m by positivity) (show (0 : ℤ) ≤ d + m - 2 * x by
        linarith)]
    omega
  have gchain : ∀ k : ℕ, ∀ y : ℤ, 2 * (y + k) ≤ d + m - 1 →
      ext (qint m * p) y ≤ ext (qint m * p) (y + k) := by
    intro k
    induction k with
    | zero => intro y _; simp
    | succ k ih =>
      intro y hy
      have h1 := ih y (by push_cast at hy; linarith)
      have h2 := gstep (y + ((k + 1 : ℕ) : ℤ)) (by push_cast at hy ⊢; linarith)
      rw [show y + ((k + 1 : ℕ) : ℤ) - 1 = y + (k : ℤ) by push_cast; ring] at h2
      exact le_trans h1 h2
  have hrefl : ∀ z : ℤ, ∃ z', 2 * z' ≤ d + m - 1 ∧ |2 * z - (d + m - 1)| = d + m - 1 - 2 * z' ∧
      ext (qint m * p) z' = ext (qint m * p) z := by
    intro z
    by_cases hz : 2 * z ≤ d + m - 1
    · exact ⟨z, hz, by rw [abs_of_nonpos (by linarith)]; ring, rfl⟩
    · exact ⟨d + m - 1 - z, by linarith, by rw [abs_of_nonneg (by linarith)]; ring, gsym z⟩
  intro x y hxy
  obtain ⟨x', hx', hxa, hxe⟩ := hrefl x
  obtain ⟨y', hy', hya, hye⟩ := hrefl y
  rw [hxa, hya] at hxy
  rw [← hxe, ← hye]
  have hk := gchain (x' - y').toNat y' (by rw [Int.toNat_of_nonneg (by linarith)]; linarith)
  rwa [Int.toNat_of_nonneg (by linarith), show y' + (x' - y') = x' by ring] at hk

/-! ### Products and sums of q-integers -/

/-- A product of q-integers. -/
noncomputable def prodQ (L : List ℕ) : ℕ[X] := (L.map qint).prod

/-- Twice its center: `∑ (m − 1)`.  Defined by recursion — written as `(L.map (· - 1)).sum` the
list is coerced to `List ℤ` through a monadic bind and no list lemma applies. -/
def dQ : List ℕ → ℤ
  | [] => 0
  | m :: L => ((m : ℤ) - 1) + dQ L

/-- A finite sum of products of q-integers. -/
noncomputable def sumQ (Ls : List (List ℕ)) : ℕ[X] := (Ls.map prodQ).sum

/-- A product of q-integers is `0` (some factor is `[0]_q`), or it is symmetric and unimodal about
`dQ L / 2`, with constant term `1` and `dQ L ≥ 0`. -/
theorem prodQ_cases (L : List ℕ) :
    prodQ L = 0 ∨ (DU (prodQ L) (dQ L) ∧ (prodQ L).coeff 0 = 1 ∧ 0 ≤ dQ L) := by
  induction L with
  | nil =>
    right
    refine ⟨by simpa [prodQ, dQ] using DU_one, by simp [prodQ], by simp [dQ]⟩
  | cons m L ih =>
    have hc : prodQ (m :: L) = qint m * prodQ L := by simp [prodQ]
    have hd : dQ (m :: L) = dQ L + m - 1 := by
      show ((m : ℤ) - 1) + dQ L = dQ L + m - 1
      ring
    by_cases hm : m = 0
    · left
      rw [hc, hm, qint_zero, zero_mul]
    rcases ih with h0 | ⟨hdu, hc0, hdn⟩
    · left
      rw [hc, h0, mul_zero]
    · right
      rw [hc, hd]
      refine ⟨DU_qmul hdu (by omega), ?_, by omega⟩
      rw [mul_coeff_zero, hc0, qint_coeff_zero (by omega), one_mul]

theorem prodQ_coeff_d (L : List ℕ) (hdu : DU (prodQ L) (dQ L)) (hc0 : (prodQ L).coeff 0 = 1)
    (hdn : 0 ≤ dQ L) : (prodQ L).coeff (dQ L).toNat = 1 := by
  have h := hdu.symm 0
  rw [sub_zero, show (0 : ℤ) = ((0 : ℕ) : ℤ) by rfl, ext_nat, hc0] at h
  rw [← ext_nat, Int.toNat_of_nonneg hdn]
  exact h

/-- One summand, compared at its own center. -/
theorem summand_le (L : List ℕ) (D i : ℕ) (hi : 2 * i < D)
    (hD : prodQ L ≠ 0 → dQ L ≤ D) : (prodQ L).coeff (D - i) ≤ (prodQ L).coeff i := by
  rcases prodQ_cases L with h0 | ⟨hdu, hc0, hdn⟩
  · simp [h0]
  · have hd := hD (by intro h; rw [h] at hc0; simp at hc0)
    have hle := hdu (i : ℤ) ((D - i : ℕ) : ℤ) (by
      rw [← sq_le_sq]
      have e : ((D - i : ℕ) : ℤ) = (D : ℤ) - i := by omega
      rw [e]
      nlinarith [mul_nonneg (show (0 : ℤ) ≤ (D : ℤ) - 2 * i by omega)
        (show (0 : ℤ) ≤ (D : ℤ) - dQ L by linarith)])
    rwa [ext_nat, ext_nat] at hle

theorem sumQ_le (Ls : List (List ℕ)) (D i : ℕ) (hi : 2 * i < D)
    (hD : ∀ L ∈ Ls, prodQ L ≠ 0 → dQ L ≤ D) :
    (sumQ Ls).coeff (D - i) ≤ (sumQ Ls).coeff i := by
  induction Ls with
  | nil => simp [sumQ]
  | cons L Ls ih =>
    have e : sumQ (L :: Ls) = prodQ L + sumQ Ls := by simp [sumQ]
    rw [e, coeff_add, coeff_add]
    exact add_le_add (summand_le L D i hi (hD L (by simp)))
      (ih (fun L' h => hD L' (by simp [h])))

theorem coeff_le_sumQ (Ls : List (List ℕ)) (L : List ℕ) (h : L ∈ Ls) (n : ℕ) :
    (prodQ L).coeff n ≤ (sumQ Ls).coeff n := by
  induction Ls with
  | nil => simp at h
  | cons L' Ls ih =>
    have e : sumQ (L' :: Ls) = prodQ L' + sumQ Ls := by simp [sumQ]
    rw [e, coeff_add]
    rcases List.mem_cons.mp h with rfl | h'
    · exact Nat.le_add_right _ _
    · exact le_trans (ih h') (Nat.le_add_left _ _)

/-- **Every finite sum of products of q-integers is bottom heavy.** -/
theorem sumQ_bottomHeavy (Ls : List (List ℕ)) : BottomHeavy (sumQ Ls) := by
  intro i hi
  apply sumQ_le Ls _ i hi
  intro L hL hne
  rcases prodQ_cases L with h0 | ⟨hdu, hc0, hdn⟩
  · exact absurd h0 hne
  · have h1 := prodQ_coeff_d L hdu hc0 hdn
    have h2 : (sumQ Ls).coeff (dQ L).toNat ≠ 0 := by
      have := coeff_le_sumQ Ls L hL (dQ L).toNat
      omega
    have h3 := le_natDegree_of_ne_zero h2
    omega

/-! ### Every entry of every family is such a sum -/

/-- Membership in the class of finite sums of products of q-integers. -/
def InC (p : ℕ[X]) : Prop := ∃ Ls : List (List ℕ), p = sumQ Ls

theorem InC.zero : InC 0 := ⟨[], by simp [sumQ]⟩

theorem InC.one : InC 1 := ⟨[[]], by simp [sumQ, prodQ]⟩

theorem InC.add {p r : ℕ[X]} (hp : InC p) (hr : InC r) : InC (p + r) := by
  obtain ⟨Ls, rfl⟩ := hp
  obtain ⟨Ls', rfl⟩ := hr
  exact ⟨Ls ++ Ls', by simp [sumQ]⟩

theorem InC.qmul {p : ℕ[X]} (m : ℕ) (hp : InC p) : InC (qint m * p) := by
  obtain ⟨Ls, rfl⟩ := hp
  refine ⟨Ls.map (m :: ·), ?_⟩
  simp only [sumQ, List.map_map]
  rw [← List.sum_map_mul_left]
  congr 1
  try (apply List.map_congr_left; intro L _; simp [prodQ])

theorem bottomHeavy_of_inC {p : ℕ[X]} (h : InC p) : BottomHeavy p := by
  obtain ⟨Ls, rfl⟩ := h
  exact sumQ_bottomHeavy Ls

theorem S_inC : ∀ n k, InC (S n k) := by
  intro n
  induction n with
  | zero => intro k; unfold S; split_ifs; exacts [InC.one, InC.zero]
  | succ n ih =>
    intro k
    cases k with
    | zero => exact InC.qmul 0 (ih 0)
    | succ k => exact InC.add (ih k) (InC.qmul (k + 1) (ih (k + 1)))

theorem c_inC : ∀ n k, InC (c n k) := by
  intro n
  induction n with
  | zero => intro k; unfold c; split_ifs; exacts [InC.one, InC.zero]
  | succ n ih =>
    intro k
    cases k with
    | zero => exact InC.qmul n (ih 0)
    | succ k => exact InC.add (ih k) (InC.qmul n (ih (k + 1)))

theorem SB_inC : ∀ n k, InC (SB n k) := by
  intro n
  induction n with
  | zero => intro k; unfold SB; split_ifs; exacts [InC.one, InC.zero]
  | succ n ih =>
    intro k
    cases k with
    | zero => exact InC.qmul 1 (ih 0)
    | succ k => exact InC.add (ih k) (InC.qmul (2 * (k + 1) + 1) (ih (k + 1)))

theorem cB_inC : ∀ n k, InC (cB n k) := by
  intro n
  induction n with
  | zero => intro k; unfold cB; split_ifs; exacts [InC.one, InC.zero]
  | succ n ih =>
    intro k
    cases k with
    | zero => exact InC.qmul (2 * n + 1) (ih 0)
    | succ k => exact InC.add (ih k) (InC.qmul (2 * n + 1) (ih (k + 1)))

/-- **MathDB #354788: Sagan–Swanson Conjecture 7.6.**  All four families are bottom heavy. -/
theorem sagan_swanson_7_6 (n k : ℕ) :
    BottomHeavy (S n k) ∧ BottomHeavy (c n k) ∧ BottomHeavy (SB n k) ∧ BottomHeavy (cB n k) :=
  ⟨bottomHeavy_of_inC (S_inC n k), bottomHeavy_of_inC (c_inC n k),
    bottomHeavy_of_inC (SB_inC n k), bottomHeavy_of_inC (cB_inC n k)⟩

end Principia.MathDB.P354788
