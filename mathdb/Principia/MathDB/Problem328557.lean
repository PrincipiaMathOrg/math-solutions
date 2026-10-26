import Mathlib
import Principia.MathDB.RootCert

/-!
# MathDB #328557 — Horwitz Conjecture 2 is FALSE

Write-up `mathdb-open-problems/problems/328557/solution.tex`,
*A positive-power counterexample for Taylor intersection roots*, 11 September 2026.

For `f z = z^n` and `r < n`, let `P c z = ∑_{k≤r} f⁽ᵏ⁾(c)/k! · (z−c)^k`.  Horwitz's
Conjecture 2 asserts that for `0 < a < b`, every **nonreal** root of `P b − P a` has real
part strictly between `a` and `b`.  The witness is `r = 5`, `n = 24`, `a = 1`, `b = 2`.

## The 215 point that nearly got missed

The conjecture constrains **nonreal** roots.  A real root would refute nothing, so `main`
proves the witness has nonzero imaginary part as well as `Re z > b` — both come from the
same disk, which sits at `Im y ≈ 0.29418` with radius `10⁻⁵`.  The write-up is also
explicit that this does NOT refute the weaker Conjecture 1, so the target stays
Conjecture 2.

## Why this row needs no square roots

#323157 and #323159 certify `|d_k|` by L2 bounds, which cost a `Real.sqrt` argument.  Here
the write-up uses `U v = |Re v| + |Im v|` above and `D v = max (|Re v|) (|Im v|)` below, and
Mathlib has both directions outright: `Complex.norm_le_abs_re_add_abs_im` and
`Complex.abs_re_le_norm` / `Complex.abs_im_le_norm`.  After scaling by `100000⁵` every
Taylor coefficient is a Gaussian **integer**, so the bounds are exact, not rounded.

Checked in SymPy before formalizing: `P₂(2+y) − P₁(2+y) = 7·Q(y)` identically; the scaled
Taylor coefficients are integral and match; self-map and contraction hold with the exact L1
bounds (Lipschitz `0.000288`); and the disk lies in `Re y ≥ 42/100000` and off the real
axis.
-/

namespace Principia.MathDB.P328557

open Principia.MathDB

/-- The order-`r` Taylor polynomial of `z ↦ z^24` at `c`, as the source defines it:
`f⁽ᵏ⁾(c)/k! = C(24,k) c^(24−k)`. -/
noncomputable def Ptay (c z : ℂ) : ℂ :=
  ∑ k ∈ Finset.range 6, ((Nat.choose 24 k : ℕ) : ℂ) * c ^ (24 - k) * (z - c) ^ k

/-- The reduced quintic: `P₂ − P₁ = 7·Q` in the variable `y = z − 2`. -/
noncomputable def Qw (y : ℂ) : ℂ :=
  2388823 + 28723560 * y + 165304680 * y ^ 2 + 606309440 * y ^ 3 + 1591706490 * y ^ 4
    + 3183470664 * y ^ 5

/-- **The reduction.**  `P₂(2+y) − P₁(2+y) = 7·Q(y)`, so the two have the same roots. -/
theorem P_diff (y : ℂ) : Ptay 2 (2 + y) - Ptay 1 (2 + y) = 7 * Qw y := by
  simp only [Ptay, Qw, Finset.sum_range_succ, Finset.sum_range_zero,
    show Nat.choose 24 0 = 1 from by decide,
    show Nat.choose 24 1 = 24 from by decide,
    show Nat.choose 24 2 = 276 from by decide,
    show Nat.choose 24 3 = 2024 from by decide,
    show Nat.choose 24 4 = 10626 from by decide,
    show Nat.choose 24 5 = 42504 from by decide]
  norm_num <;> ring

/-- Taylor coefficients of `Q` about `c = (43+29418i)/100000`, scaled by `100000⁵`. -/
noncomputable def dc : ℕ → ℂ
  | 0 => -721604472283649306702389608 + 165645513530567870032885392 * Complex.I
  | 1 => -1004676921887779274293352280 - 6506943736472612850767400000 * Complex.I
  | 2 => -663960967491839332602960 - 272962542773092446347040 * Complex.I
  | 3 => -21459820585302550000 + 18810468761522454720 * Complex.I
  | 4 => 159855095192760 + 468256699967760 * Complex.I
  | 5 => 3183470664
  | _ => 0

/-- **The Taylor expansion** in `w = 100000(y − c)`, closed by `linear_combination` against
`Complex.I_sq` with the exact quotient of `LHS − RHS` by `I² + 1`. -/
theorem Q_taylor (w : ℂ) :
    (100000 : ℂ) ^ 5 * Qw ((43 + 29418 * Complex.I + w) / 100000)
      = ∑ k ∈ Finset.range 6, dc k * w ^ k := by
  simp only [Qw, dc, Finset.sum_range_succ, Finset.sum_range_zero]
  linear_combination
    (70140130616724354585060405841152*Complex.I^3
      + 11921294890326391084550344320*Complex.I^2*w
      + 119723404463204353303081888805760*Complex.I^2
      + 810476231581099400676480*Complex.I*w^2
      + 16278931873438623061130177280*Complex.I*w
      + 84918006283528465214576340970368*Complex.I + 27550351199303127360*w^3
      + 830049555039701359429440*w^2 + 3891282807027557497913121600*w
      + 24012769043428690881144202205760) * Complex.I_sq

/-- The exact L1 upper bounds `U(d_k) = |Re d_k| + |Im d_k|`. -/
noncomputable def Uk : ℕ → ℝ
  | 0 => 887249985814217176735275000
  | 1 => 7511620658360392125060752280
  | 2 => 936923510264931778950000
  | 3 => 40270289346825004720
  | 4 => 628111795160520
  | 5 => 3183470664
  | _ => 0

/-- The exact L∞ lower bound `D(d₁) = max |Re d₁| |Im d₁|`. -/
noncomputable def Lb : ℝ := 6506943736472612850767400000

/-- `Icc 2 5` as `range 6` minus its first two terms. -/
theorem sum_Icc_eq (g : ℕ → ℝ) :
    ∑ k ∈ Finset.Icc (2 : ℕ) 5, g k = (∑ k ∈ Finset.range 6, g k) - g 0 - g 1 := by
  have hset : Finset.range 6 = insert 0 (insert 1 (Finset.Icc (2 : ℕ) 5)) := by
    ext j
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [hset, Finset.sum_insert (by decide), Finset.sum_insert (by decide)]
  ring

/-- `|d_k| ≤ U_k`, straight from the triangle inequality — no square roots. -/
theorem dc_bound : ∀ k ≤ 5, ‖dc k‖ ≤ Uk k := by
  intro k hk
  interval_cases k <;>
    refine le_trans (Complex.norm_le_abs_re_add_abs_im _) ?_ <;> simp [dc, Uk] <;> norm_num

/-- `L ≤ |d₁|`, from `|Im z| ≤ ‖z‖`. -/
theorem dc1_lower : Lb ≤ ‖dc 1‖ := by
  refine le_trans ?_ (Complex.abs_im_le_norm (dc 1))
  simp [dc, Lb] <;> norm_num

/-- The disk maps into itself. -/
theorem hself : Uk 0 + ∑ k ∈ Finset.Icc (2 : ℕ) 5, Uk k * (1 : ℝ) ^ k ≤ Lb * 1 := by
  rw [sum_Icc_eq]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Uk, Lb]
  norm_num

/-- The map is a contraction on the disk. -/
theorem hlip :
    ∑ k ∈ Finset.Icc (2 : ℕ) 5, (k : ℝ) * Uk k * (1 : ℝ) ^ (k - 1) < Lb := by
  rw [sum_Icc_eq]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Uk, Lb]
  norm_num

/-- `Q` has a zero in `|w| ≤ 1`, i.e. `|y − c| ≤ 10⁻⁵`. -/
theorem root_exists : ∃ w : ℂ, ‖w‖ ≤ 1 ∧ ∑ k ∈ Finset.range 6, dc k * w ^ k = 0 :=
  RootCert.exists_root_of_contraction' dc Uk Lb 1 5 (by norm_num) (by norm_num)
    (by norm_num [Lb]) dc1_lower dc_bound hself hlip

/-- **MathDB #328557 — Horwitz Conjecture 2 is FALSE.**  `P₂ − P₁` has a NONREAL root whose
real part exceeds `b = 2`, so it is not strictly between `a` and `b`.  Both facts come from
the same disk: `100000·(z−2) = 43 + 29418i + w` with `‖w‖ ≤ 1`. -/
theorem main : ∃ z : ℂ, z.im ≠ 0 ∧ 2 < z.re ∧ Ptay 2 z - Ptay 1 z = 0 := by
  obtain ⟨w, hw, hsum⟩ := root_exists
  refine ⟨2 + (43 + 29418 * Complex.I + w) / 100000, ?_, ?_, ?_⟩
  · -- `100000 · Im z = 29418 + Im w ≥ 29417 > 0`
    have hz : (100000 : ℂ) * ((43 + 29418 * Complex.I + w) / 100000)
        = 43 + 29418 * Complex.I + w := by field_simp
    have him := congrArg Complex.im hz
    simp only [Complex.mul_im, Complex.mul_re, Complex.add_im, Complex.add_re,
      Complex.re_ofNat, Complex.im_ofNat, Complex.I_re, Complex.I_im] at him
    have h1 : |w.im| ≤ ‖w‖ := Complex.abs_im_le_norm w
    have h2 : -‖w‖ ≤ w.im := (abs_le.mp h1).1
    simp only [Complex.add_im, Complex.re_ofNat, Complex.im_ofNat]
    intro hc
    nlinarith [him, h2, hw, hc]
  · -- `100000 · (Re z − 2) = 43 + Re w ≥ 42 > 0`
    have hz : (100000 : ℂ) * ((43 + 29418 * Complex.I + w) / 100000)
        = 43 + 29418 * Complex.I + w := by field_simp
    have hre := congrArg Complex.re hz
    simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.re_ofNat, Complex.im_ofNat, Complex.I_re, Complex.I_im] at hre
    have h1 : |w.re| ≤ ‖w‖ := Complex.abs_re_le_norm w
    have h2 : -‖w‖ ≤ w.re := (abs_le.mp h1).1
    simp only [Complex.add_re, Complex.re_ofNat]
    nlinarith [hre, h2, hw]
  · rw [P_diff]
    have h5 : (100000 : ℂ) ^ 5 ≠ 0 := by norm_num
    have hQ : Qw ((43 + 29418 * Complex.I + w) / 100000) = 0 := by
      have := Q_taylor w
      rw [hsum] at this
      exact (mul_eq_zero.mp this).resolve_left h5
    rw [hQ, mul_zero]

end Principia.MathDB.P328557
