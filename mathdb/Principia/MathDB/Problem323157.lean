import Mathlib
import Principia.MathDB.RootCert
import Principia.MathDB.Problem323157Poly

/-!
# MathDB #323157 — the refutation

Part 2 of the counterexample to Karp's Conjecture 2 (write-up
`mathdb-open-problems/problems/323157/solution.tex`).  `Problem323157Poly` supplies the
hypothesis checks and the reduction `Q = 5280 P` with `P`'s Taylor expansion about
`c = 1 + 22i`; this module discharges the two numeric inequalities of
`RootCert.exists_root_of_contraction'` and assembles `main`.

The write-up certifies the disk by **Rouché**, which Mathlib does not have.  It is not needed:
refuting stability requires only that *a* zero exist with non-negative real part, never a count
of zeros, and the write-up's own bounds are exactly the hypotheses of a contraction — see
`Principia.MathDB.RootCert`.

`U_k = 1 + ⌊|d_k|⌋` and `L = ⌊|d_1|⌋` are the write-up's table, reproduced exactly in Python
before formalizing; the contraction constant is `0.1199 < 1` and the disk `|w| ≤ 1/4` about
`c` lies in `Re ≥ 3/4 > 0`.
-/

namespace Principia.MathDB.P323157

/-- The write-up's `U_k = 1 + ⌊|d_k|⌋`, so `|d_k| < U_k`. -/
noncomputable def Uk : ℕ → ℝ
  | 0 => 816065210715919818
  | 1 => 4713796926694788092
  | 2 => 1088281691451296882
  | 3 => 110502641723796844
  | 4 => 6548680002689171
  | 5 => 250999762004696
  | 6 => 6478398028259
  | 7 => 112919703186
  | 8 => 1283564680
  | 9 => 8631961
  | 10 => 26112
  | _ => 0

/-- The write-up's `L = ⌊|d_1|⌋`, so `L ≤ |d_1|`. -/
noncomputable def Lb : ℝ := 4713796926694788091

/-- `‖z‖ ≤ c` from an integer bound on `re² + im²`. -/
theorem norm_le_of_sq (z : ℂ) (c : ℝ) (hc : 0 ≤ c) (h : z.re ^ 2 + z.im ^ 2 ≤ c ^ 2) :
    ‖z‖ ≤ c := by
  rw [Complex.norm_def, Complex.normSq_apply]
  calc Real.sqrt (z.re * z.re + z.im * z.im) ≤ Real.sqrt (c ^ 2) := by
        apply Real.sqrt_le_sqrt
        nlinarith
    _ = c := Real.sqrt_sq hc

/-- `c ≤ ‖z‖` from an integer bound on `re² + im²`. -/
theorem le_norm_of_sq (z : ℂ) (c : ℝ) (hc : 0 ≤ c) (h : c ^ 2 ≤ z.re ^ 2 + z.im ^ 2) :
    c ≤ ‖z‖ := by
  rw [Complex.norm_def, Complex.normSq_apply]
  calc c = Real.sqrt (c ^ 2) := (Real.sqrt_sq hc).symm
    _ ≤ Real.sqrt (z.re * z.re + z.im * z.im) := by
        apply Real.sqrt_le_sqrt
        nlinarith

/-- Rewrite a sum over `Icc 2 10` as one over `range 11`, which expands deterministically. -/
theorem sum_Icc_eq (f : ℕ → ℝ) :
    ∑ k ∈ Finset.Icc (2 : ℕ) 10, f k = (∑ k ∈ Finset.range 11, f k) - f 0 - f 1 := by
  have hset : Finset.range 11 = insert 0 (insert 1 (Finset.Icc (2 : ℕ) 10)) := by
    ext j
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [hset, Finset.sum_insert (by decide), Finset.sum_insert (by decide)]
  ring

/-- `|d_k| ≤ U_k` for every index the certificate covers. -/
theorem dc_bound : ∀ k ≤ 10, ‖dc k‖ ≤ Uk k := by
  intro k hk
  interval_cases k <;> refine norm_le_of_sq _ _ (by norm_num [Uk]) ?_ <;>
    simp [dc, Uk] <;> norm_num

/-- `L ≤ |d_1|`. -/
theorem dc1_lower : Lb ≤ ‖dc 1‖ := by
  refine le_norm_of_sq _ _ (by norm_num [Lb]) ?_
  simp [dc, Lb] <;> norm_num

/-- The disk maps into itself. -/
theorem hself : Uk 0 + ∑ k ∈ Finset.Icc (2 : ℕ) 10, Uk k * (1 / 4 : ℝ) ^ k ≤ Lb * (1 / 4) := by
  rw [sum_Icc_eq]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Uk, Lb]
  norm_num

/-- The map is a contraction on the disk. -/
theorem hlip :
    ∑ k ∈ Finset.Icc (2 : ℕ) 10, (k : ℝ) * Uk k * (1 / 4 : ℝ) ^ (k - 1) < Lb := by
  rw [sum_Icc_eq]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Uk, Lb]
  norm_num

/-- `P` has a zero in the disk `|w| ≤ 1/4` about `c = 1 + 22i`. -/
theorem root_exists : ∃ w : ℂ, ‖w‖ ≤ 1 / 4 ∧ ∑ k ∈ Finset.range 11, dc k * w ^ k = 0 :=
  RootCert.exists_root_of_contraction' dc Uk Lb (1 / 4) 10 (by norm_num) (by norm_num)
    (by norm_num [Lb]) dc1_lower dc_bound hself hlip

/-- **MathDB #323157 — Karp's Conjecture 2 is FALSE.**  The witness `n = 12`, `α = 1`,
`β = 40`, `f = (1,45,46,47,48,49,50,49,48,47,46,45,1)` satisfies the conjecture's hypotheses
(`fpos`, `flogconcave`) yet `Q` has a zero with strictly positive real part, so not every zero
has negative real part. -/
theorem main : ∃ z : ℂ, 0 < z.re ∧ Qgen fv 1 40 12 z = 0 := by
  obtain ⟨w, hw, hsum⟩ := root_exists
  refine ⟨1 + 22 * Complex.I + w, ?_, ?_⟩
  · refine RootCert.re_pos_of_norm_le (1 + 22 * Complex.I) w (1 / 4) hw ?_
    simp <;> norm_num
  · rw [Q_eq, P_taylor, hsum, mul_zero]

end Principia.MathDB.P323157
