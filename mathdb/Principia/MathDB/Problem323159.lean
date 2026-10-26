import Mathlib
import Principia.MathDB.RootCert
import Principia.MathDB.Problem323157

/-!
# MathDB #323159 — Karp's Conjecture 5 is FALSE

Write-up `mathdb-open-problems/problems/323159/solution.tex`,
*A counterexample to the higher Toeplitz Hurwitz-stability conjecture*, 11 September 2026.

Karp's Conjecture 5 asserts that `P_n^r` is Hurwitz stable whenever the input lies in
`PF_r`, for `r ≥ 2`.  At `r = 2` the source gives
`P_n^2 x = ∑_{k≤n} C(n,k) f k f (n-k) ((x)_k (x)_{n-k} − (x+1)_k (x−1)_{n-k})`,
and the witness is `n = 15`, `f = (1,51,52,53,54,55,56,57,57,56,55,54,53,52,51,1)`.

## The 215 point, and it is not cosmetic

The hypothesis here is **`PF₂`** — every 2×2 minor of the infinite Toeplitz matrix of `f`
is nonnegative — and **not** the strict log-concavity that #323157's conjecture asks for.
Reusing that row's hypothesis checks would certify a conjecture nobody stated.  Both are
proved below: `flogconcave` because the write-up quotes it, `pf2_core` because the
conjecture needs it.

`PF₂` quantifies over an infinite matrix but is finite: the minor is
`f a * f (a+h−d) − f (a+h) * f (a−d)`, and `f (a+h) * f (a−d) ≠ 0` forces `0 ≤ a−d` and
`a+h ≤ 15`, so off that window the minor is a product of nonnegatives.

Checked in SymPy before formalizing: `deg P₁₅² = 13`; `P₁₅² = 210 · (x+1)₇ · R` exactly;
all fourteen log-concavity gaps strict; `PF₂` with zero violations over the full range; and
the write-up's transformed coefficients are exactly `20⁶ ×` the Taylor coefficients of `R`
about `(1+41i)/10` in `w = 20(x−c)` — that scale clears denominators, it does not
approximate.
-/

namespace Principia.MathDB.P323159

open Principia.MathDB

/-- The witness sequence, over `ℤ` so the hypothesis checks are decidable. -/
def fn : ℕ → ℤ
  | 0 => 1
  | 1 => 51
  | 2 => 52
  | 3 => 53
  | 4 => 54
  | 5 => 55
  | 6 => 56
  | 7 => 57
  | 8 => 57
  | 9 => 56
  | 10 => 55
  | 11 => 54
  | 12 => 53
  | 13 => 52
  | 14 => 51
  | 15 => 1
  | _ => 0

/-- The witness in `ℂ`, where `P` lives. -/
noncomputable def fv (k : ℕ) : ℂ := ((fn k : ℤ) : ℂ)

/-- The rising factorial `(y)_k`. -/
noncomputable def rise (y : ℂ) (k : ℕ) : ℂ := ∏ i ∈ Finset.range k, (y + (i : ℂ))

/-- Karp's `P_n^2`, stated exactly as the source states it. -/
noncomputable def Pgen (g : ℕ → ℂ) (n : ℕ) (x : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), ((n.choose k : ℕ) : ℂ) * g k * g (n - k) *
    (rise x k * rise x (n - k) - rise (x + 1) k * rise (x - 1) (n - k))

/-- The degree-6 cofactor, after dividing out `210 · (x+1)₇`. -/
noncomputable def Rw (x : ℂ) : ℂ :=
  3212352000 + 2128319736 * x + 736979998 * x ^ 2 + 192645735 * x ^ 3 + 36750955 * x ^ 4
    + 4104969 * x ^ 5 + 191647 * x ^ 6

/-- **The factorization.**  `P₁₅² = 210 · (x+1)₇ · R`.  The binomial coefficients are
supplied as kernel-checked `ℕ` facts, since `simp` does not reduce `Nat.choose` on
numerals. -/
theorem P_eq (x : ℂ) : Pgen fv 15 x = 210 * rise (x + 1) 7 * Rw x := by
  simp only [Pgen, rise, fv, fn, Rw, Finset.sum_range_succ, Finset.sum_range_zero,
    Finset.prod_range_succ, Finset.prod_range_zero,
    show Nat.choose 15 0 = 1 from by decide,
    show Nat.choose 15 1 = 15 from by decide,
    show Nat.choose 15 2 = 105 from by decide,
    show Nat.choose 15 3 = 455 from by decide,
    show Nat.choose 15 4 = 1365 from by decide,
    show Nat.choose 15 5 = 3003 from by decide,
    show Nat.choose 15 6 = 5005 from by decide,
    show Nat.choose 15 7 = 6435 from by decide,
    show Nat.choose 15 8 = 6435 from by decide,
    show Nat.choose 15 9 = 5005 from by decide,
    show Nat.choose 15 10 = 3003 from by decide,
    show Nat.choose 15 11 = 1365 from by decide,
    show Nat.choose 15 12 = 455 from by decide,
    show Nat.choose 15 13 = 105 from by decide,
    show Nat.choose 15 14 = 15 from by decide,
    show Nat.choose 15 15 = 1 from by decide]
  norm_num <;> ring

/-- Taylor coefficients of `R` about `c = (1+41i)/10`, scaled by `20⁶`. -/
noncomputable def dc : ℕ → ℂ
  | 0 => 6242984901271040 - 4815010659523584 * Complex.I
  | 1 => -7146943743914496 - 9080441566052096 * Complex.I
  | 2 => -369163407187520 - 56477312908800 * Complex.I
  | 3 => -4012914867840 + 2981422413440 * Complex.I
  | 4 => -3796641800 + 34603649040 * Complex.I
  | 5 => 84399144 + 94290324 * Complex.I
  | 6 => 191647
  | _ => 0

/-- **The Taylor expansion** in `w = 20(x − c)`.  `ring` treats `Complex.I` as an atom and
never applies `I² = −1`, so this closes by `linear_combination` against `Complex.I_sq`
with the exact quotient of `LHS − RHS` by `I² + 1` — the division is exact. -/
theorem R_taylor (w : ℂ) :
    (20 : ℂ) ^ 6 * Rw ((2 + 82 * Complex.I + w) / 20)
      = ∑ k ∈ Finset.range 7, dc k * w ^ k := by
  simp only [Rw, dc, Finset.sum_range_succ, Finset.sum_range_zero]
  linear_combination
    (58261966558395328*Complex.I^4 + 4263070723785024*Complex.I^3*w
      + 312901254127742208*Complex.I^3 + 129971668408080*Complex.I^2*w^2
      + 19079344763886720*Complex.I^2*w + 644013094546977792*Complex.I^2
      + 2113360461920*Complex.I*w^3 + 465349872289920*Complex.I*w^2
      + 29994249330135616*Complex.I*w + 603518442298474752*Complex.I + 19329516420*w^4
      + 5674998442560*w^3 + 496686625261200*w^2 + 14448205105365120*w
      + 213453023780446528) * Complex.I_sq

/-- Every entry is positive. -/
theorem fpos : ∀ k ≤ 15, 0 < fn k := by decide

/-- Strict log-concavity at every `k` with `1 ≤ k < 15` — all fourteen. -/
theorem flogconcave : ∀ k < 15, 1 ≤ k → fn (k - 1) * fn (k + 1) < fn k ^ 2 := by decide

/-- `f` is nonnegative on its support. -/
theorem fn_nonneg : ∀ k ≤ 15, 0 ≤ fn k := by decide

/-- The bounded core of `PF₂`: every 2×2 minor whose second product is nonzero. -/
theorem pf2_core : ∀ a ≤ 15, ∀ h ≤ 15, ∀ d ≤ 15, d ≤ a → a + h ≤ 15 →
    fn (a - d) * fn (a + h) ≤ fn a * fn (a + h - d) := by decide

/-- The infinite Toeplitz symbol: `f` extended by zero off `[0,15]`.

The bound is written into the `if` rather than left to `fn`'s catch-all branch on purpose:
`fn` is a pattern match on `ℕ`, which does NOT reduce at a symbolic index like `m + 16`, so
a proof that `fn` vanishes beyond 15 would have to fight well-founded reduction.  Carrying
the bound in the guard makes vanishing immediate and costs nothing. -/
def fz (a : ℤ) : ℤ := if 0 ≤ a ∧ a ≤ 15 then fn a.toNat else 0

/-- Inside the window, `fz` is just `fn`. -/
theorem fz_of_mem {a : ℤ} (h0 : 0 ≤ a) (h1 : a ≤ 15) : fz a = fn a.toNat := by
  unfold fz
  rw [if_pos ⟨h0, h1⟩]

/-- `fz` is nonnegative everywhere. -/
theorem fz_nonneg (a : ℤ) : 0 ≤ fz a := by
  unfold fz
  split
  · rename_i h
    exact fn_nonneg _ (by omega)
  · exact le_refl 0

/-- A nonzero value pins the index into the window. -/
theorem fz_bounds {a : ℤ} (h : fz a ≠ 0) : 0 ≤ a ∧ a ≤ 15 := by
  unfold fz at h
  split at h
  · assumption
  · exact absurd rfl h

/-- **`PF₂`** — every 2×2 minor of the infinite Toeplitz matrix of `f` is nonnegative.
This, not log-concavity, is the hypothesis Karp's Conjecture 5 imposes. -/
theorem pf2 (a s t : ℤ) (hs : 0 < s) (ht : 0 < t) :
    0 ≤ fz a * fz (a + s - t) - fz (a + s) * fz (a - t) := by
  rcases eq_or_ne (fz (a + s)) 0 with e | e
  · rw [e, zero_mul, sub_zero]
    exact mul_nonneg (fz_nonneg _) (fz_nonneg _)
  rcases eq_or_ne (fz (a - t)) 0 with e2 | e2
  · rw [e2, mul_zero, sub_zero]
    exact mul_nonneg (fz_nonneg _) (fz_nonneg _)
  obtain ⟨p0, p1⟩ := fz_bounds e
  obtain ⟨q0, q1⟩ := fz_bounds e2
  -- each rewrite is stated as a `have` so the implicit index is pinned by the ascription;
  -- `rw [fz_of_mem (by omega) ..]` cannot determine it
  have r1 : fz a = fn a.toNat := fz_of_mem (by omega) (by omega)
  have r2 : fz (a + s - t) = fn (a + s - t).toNat := fz_of_mem (by omega) (by omega)
  have r3 : fz (a + s) = fn (a + s).toNat := fz_of_mem p0 p1
  have r4 : fz (a - t) = fn (a - t).toNat := fz_of_mem q0 q1
  have h1 : (a + s).toNat = a.toNat + s.toNat := by omega
  have h2 : (a - t).toNat = a.toNat - t.toNat := by omega
  have h3 : (a + s - t).toNat = a.toNat + s.toNat - t.toNat := by omega
  rw [r1, r2, r3, r4, h1, h2, h3]
  have key := pf2_core a.toNat (by omega) s.toNat (by omega) t.toNat (by omega)
    (by omega) (by omega)
  -- `omega` cannot close this: the terms are PRODUCTS of variables.  `linarith` treats
  -- each product as an atom, which is exactly what is needed.
  linarith [key]

/-- The write-up's `U_k = 1 + ⌊|d_k|⌋` (exact at `k = 6`, where `d₆` is real). -/
noncomputable def Uk : ℕ → ℝ
  | 0 => 7884109850124104
  | 1 => 11555657658184808
  | 2 => 373458576122838
  | 3 => 4999236476093
  | 4 => 34811305863
  | 5 => 126545963
  | 6 => 191647
  | _ => 0

/-- The write-up's `L = ⌊|d₁|⌋`. -/
noncomputable def Lb : ℝ := 11555657658184807

/-- `Icc 2 6` as `range 7` minus its first two terms, which expands deterministically. -/
theorem sum_Icc_eq (g : ℕ → ℝ) :
    ∑ k ∈ Finset.Icc (2 : ℕ) 6, g k = (∑ k ∈ Finset.range 7, g k) - g 0 - g 1 := by
  have hset : Finset.range 7 = insert 0 (insert 1 (Finset.Icc (2 : ℕ) 6)) := by
    ext j
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [hset, Finset.sum_insert (by decide), Finset.sum_insert (by decide)]
  ring

/-- `|d_k| ≤ U_k` for every index the certificate covers. -/
theorem dc_bound : ∀ k ≤ 6, ‖dc k‖ ≤ Uk k := by
  intro k hk
  interval_cases k <;>
    refine P323157.norm_le_of_sq _ _ (by norm_num [Uk]) ?_ <;> simp [dc, Uk] <;> norm_num

/-- `L ≤ |d₁|`. -/
theorem dc1_lower : Lb ≤ ‖dc 1‖ := by
  refine P323157.le_norm_of_sq _ _ (by norm_num [Lb]) ?_
  simp [dc, Lb] <;> norm_num

/-- The disk maps into itself. -/
theorem hself : Uk 0 + ∑ k ∈ Finset.Icc (2 : ℕ) 6, Uk k * (1 : ℝ) ^ k ≤ Lb * 1 := by
  rw [sum_Icc_eq]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Uk, Lb]
  norm_num

/-- The map is a contraction on the disk. -/
theorem hlip :
    ∑ k ∈ Finset.Icc (2 : ℕ) 6, (k : ℝ) * Uk k * (1 : ℝ) ^ (k - 1) < Lb := by
  rw [sum_Icc_eq]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Uk, Lb]
  norm_num

/-- `R` has a zero in `|w| ≤ 1`, i.e. `|x − c| ≤ 1/20`. -/
theorem root_exists : ∃ w : ℂ, ‖w‖ ≤ 1 ∧ ∑ k ∈ Finset.range 7, dc k * w ^ k = 0 :=
  RootCert.exists_root_of_contraction' dc Uk Lb 1 6 (by norm_num) (by norm_num)
    (by norm_num [Lb]) dc1_lower dc_bound hself hlip

/-- **MathDB #323159 — Karp's Conjecture 5 is FALSE.**  The witness is `PF₂` (`pf2`) and
strictly log-concave (`flogconcave`), yet `P₁₅²` has a zero with `Re z > 0` — indeed
`Re z ≥ 1/20`, since the disk `|w| ≤ 1` in `w = 20(x − c)` sits in `Re x ≥ 1/20`. -/
theorem main : ∃ z : ℂ, 0 < z.re ∧ Pgen fv 15 z = 0 := by
  obtain ⟨w, hw, hsum⟩ := root_exists
  refine ⟨(2 + 82 * Complex.I + w) / 20, ?_, ?_⟩
  · -- `20 * z = 2 + 82i + w`, so `20 · Re z = 2 + Re w ≥ 1`
    have hz : (20 : ℂ) * ((2 + 82 * Complex.I + w) / 20) = 2 + 82 * Complex.I + w := by
      field_simp
    have hre := congrArg Complex.re hz
    simp only [Complex.mul_re, Complex.add_re, Complex.re_ofNat, Complex.im_ofNat,
      Complex.mul_im, Complex.I_re, Complex.I_im] at hre
    have h1 : |w.re| ≤ ‖w‖ := Complex.abs_re_le_norm w
    have h2 : -‖w‖ ≤ w.re := (abs_le.mp h1).1
    nlinarith [hre, h2, hw]
  · rw [P_eq]
    have h20 : (20 : ℂ) ^ 6 ≠ 0 := by norm_num
    have hR : Rw ((2 + 82 * Complex.I + w) / 20) = 0 := by
      have := R_taylor w
      rw [hsum] at this
      exact (mul_eq_zero.mp this).resolve_left h20
    rw [hR, mul_zero]

end Principia.MathDB.P323159
