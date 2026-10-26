import Mathlib

/-!
# MathDB #341671 — the taxicab Erdős–Mordell inequality `∑ xᵢ ≥ (3/2) ∑ dᵢ`

Write-up: `antoshashakov/Principia-Math-In-Progress`, branch `mathdb-results`,
`mathdb-open-problems/problems/341671/solution.tex`, proving Conjecture 1 of Petrović, Malešević
and Banjac: for an interior point `P` of a taxicab triangle `A₁A₂A₃`, the sum of the distances from
`P` to the vertices is at least `3/2` times the sum of its distances to the three side lines.

**What is proved, and why it is stronger than the conjecture.**  `erdos_mordell` holds in every
real normed space, for side LINES and (`erdos_mordell_segments`) for side SEGMENTS.  "Strictly
interior" is encoded as the write-up uses it: positive barycentric coordinates `αᵢ > 0`,
`∑ αᵢ = 1`, `P = ∑ αᵢ Aᵢ`.  Nondegeneracy of the triangle is never used, so it is not a hypothesis;
dropping a hypothesis only strengthens the theorem.  `taxicab_erdos_mordell` specializes to the
taxicab plane `PiLp 1 (fun _ : Fin 2 => ℝ)`, which is the conjecture as posed.

**Route (the write-up's).**  With `Qᵢ` the point of the opposite side with barycentric weights
`αⱼ/(1 − αᵢ)`, `(1 − αᵢ)(P − Qᵢ) = αᵢ(Aᵢ − P)`, whence `dᵢ ≤ αᵢ(dᵢ + xᵢ)`, so
`Φ = ∑ dᵢ/(dᵢ + xᵢ) ≤ 1`; and `xᵢ ≥ dⱼ` for `i ≠ j` because `Aᵢ` lies on side `j`.  The algebraic
Lemma then gives the inequality: sort `d₁ ≥ d₂ ≥ d₃`, compare with the baseline
`b = (d₂, d₁, d₁)`, bound each term of `Φ` below by its tangent line with common slope
`K = d₁/(d₁ + d₂)²`, and close with
`2d₃(d₁ + d₂)² − d₁(d₂ + 3d₃ − d₁)(d₁ + d₃) = d₁²(d₁ − d₂) + 3d₁d₃(d₂ − d₃) + 2d₂²d₃ ≥ 0`
(checked in SymPy).  The proof also covers zero distances, which the write-up excludes.

**Not formalized here:** the write-up's sharpness example (`3/2` optimal in the taxicab plane).
-/

namespace Principia.MathDB.P341671

open Metric

/-- The tangent-line bound `d/(d+x) ≥ d/(d+b) − d/(d+b)² · (x − b)` for `x ≥ b`. -/
theorem tangent {d b x : ℝ} (hd : 0 ≤ d) (hb : 0 < d + b) (hx : b ≤ x) :
    d / (d + b) - d / (d + b) ^ 2 * (x - b) ≤ d / (d + x) := by
  have hc : 0 < d + x := by linarith
  have nb := hb.ne'
  have nc := hc.ne'
  have key : d / (d + x) - (d / (d + b) - d / (d + b) ^ 2 * (x - b))
      = d * (x - b) ^ 2 / ((d + b) ^ 2 * (d + x)) := by
    field_simp <;> ring
  have : 0 ≤ d * (x - b) ^ 2 / ((d + b) ^ 2 * (d + x)) :=
    div_nonneg (mul_nonneg hd (sq_nonneg _)) (mul_pos (pow_pos hb 2) hc).le
  linarith

/-- The algebraic lemma with the distances sorted, `d₁ ≥ d₂ ≥ d₃ ≥ 0`. -/
theorem core (d1 d2 d3 x1 x2 x3 : ℝ) (h12 : d2 ≤ d1) (h23 : d3 ≤ d2) (hd3 : 0 ≤ d3)
    (hx1 : d2 ≤ x1) (hx2 : d1 ≤ x2) (hx3 : d1 ≤ x3)
    (hphi : d1 / (d1 + x1) + d2 / (d2 + x2) + d3 / (d3 + x3) ≤ 1) :
    3 / 2 * (d1 + d2 + d3) ≤ x1 + x2 + x3 := by
  have hd2 : 0 ≤ d2 := hd3.trans h23
  rcases eq_or_lt_of_le (hd2.trans h12) with h0 | hd1
  · linarith
  by_contra hcon
  push_neg at hcon
  by_cases hA : 3 / 2 * (d1 + d2 + d3) ≤ d2 + 2 * d1
  · linarith
  push_neg at hA
  have ha : 0 < d1 + d2 := by linarith
  have hb : 0 < d3 + d1 := by linarith
  have hKpos : 0 < d1 / (d1 + d2) ^ 2 := div_pos hd1 (pow_pos ha 2)
  have t1 := tangent hd1.le ha hx1
  have t2 := tangent hd2 (show 0 < d2 + d1 by linarith) hx2
  have t3 := tangent hd3 hb hx3
  have k2 : d2 / (d2 + d1) ^ 2 ≤ d1 / (d1 + d2) ^ 2 := by
    rw [add_comm d2 d1]
    exact div_le_div_of_nonneg_right h12 (sq_nonneg _)
  have k3 : d3 / (d3 + d1) ^ 2 ≤ d1 / (d1 + d2) ^ 2 := by
    rw [div_le_div_iff₀ (pow_pos hb 2) (pow_pos ha 2)]
    nlinarith [mul_nonneg hd3 (mul_nonneg (by linarith : (0 : ℝ) ≤ d1 - d2)
      (by linarith : (0 : ℝ) ≤ 3 * d1 + d2)), mul_nonneg hd1.le (sq_nonneg (d1 - d3))]
  have m2 : d2 / (d2 + d1) ^ 2 * (x2 - d1) ≤ d1 / (d1 + d2) ^ 2 * (x2 - d1) :=
    mul_le_mul_of_nonneg_right k2 (by linarith)
  have m3 : d3 / (d3 + d1) ^ 2 * (x3 - d1) ≤ d1 / (d1 + d2) ^ 2 * (x3 - d1) :=
    mul_le_mul_of_nonneg_right k3 (by linarith)
  have hsum : d1 / (d1 + d2) + d2 / (d2 + d1) = 1 := by
    rw [add_comm d2 d1, ← add_div, div_self ha.ne']
  have hS : (x1 - d2) + (x2 - d1) + (x3 - d1) < (d2 + 3 * d3 - d1) / 2 := by linarith
  have hKS : d1 / (d1 + d2) ^ 2 * ((x1 - d2) + (x2 - d1) + (x3 - d1))
      < d1 / (d1 + d2) ^ 2 * ((d2 + 3 * d3 - d1) / 2) :=
    mul_lt_mul_of_pos_left hS hKpos
  have hfin : d1 / (d1 + d2) ^ 2 * ((d2 + 3 * d3 - d1) / 2) ≤ d3 / (d3 + d1) := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (pow_pos ha 2) hb]
    nlinarith [mul_nonneg (mul_nonneg hd1.le hd1.le) (sub_nonneg.2 h12),
      mul_nonneg (mul_nonneg hd1.le hd3) (sub_nonneg.2 h23), mul_nonneg (sq_nonneg d2) hd3]
  linarith

/-- **The algebraic lemma of the write-up**, unsorted: `xᵢ ≥ dⱼ` for `i ≠ j`, `dᵢ ≥ 0` and
`∑ dᵢ/(dᵢ + xᵢ) ≤ 1` give `∑ xᵢ ≥ (3/2) ∑ dᵢ`. -/
theorem algebra (d1 d2 d3 x1 x2 x3 : ℝ) (hd1 : 0 ≤ d1) (hd2 : 0 ≤ d2) (hd3 : 0 ≤ d3)
    (h12 : d2 ≤ x1) (h13 : d3 ≤ x1) (h21 : d1 ≤ x2) (h23 : d3 ≤ x2) (h31 : d1 ≤ x3)
    (h32 : d2 ≤ x3) (hphi : d1 / (d1 + x1) + d2 / (d2 + x2) + d3 / (d3 + x3) ≤ 1) :
    3 / 2 * (d1 + d2 + d3) ≤ x1 + x2 + x3 := by
  rcases le_total d2 d1 with a | a <;> rcases le_total d3 d2 with b | b <;>
    rcases le_total d3 d1 with c | c
  all_goals first
    | linarith [core d1 d2 d3 x1 x2 x3 (by linarith) (by linarith) (by linarith) (by linarith)
        (by linarith) (by linarith) (by linarith)]
    | linarith [core d1 d3 d2 x1 x3 x2 (by linarith) (by linarith) (by linarith) (by linarith)
        (by linarith) (by linarith) (by linarith)]
    | linarith [core d2 d1 d3 x2 x1 x3 (by linarith) (by linarith) (by linarith) (by linarith)
        (by linarith) (by linarith) (by linarith)]
    | linarith [core d2 d3 d1 x2 x3 x1 (by linarith) (by linarith) (by linarith) (by linarith)
        (by linarith) (by linarith) (by linarith)]
    | linarith [core d3 d1 d2 x3 x1 x2 (by linarith) (by linarith) (by linarith) (by linarith)
        (by linarith) (by linarith) (by linarith)]
    | linarith [core d3 d2 d1 x3 x2 x1 (by linarith) (by linarith) (by linarith) (by linarith)
        (by linarith) (by linarith) (by linarith)]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- One side: if `Q = lineMap B C (c/(b+c))` lies in `S`, then `d ≤ a(d + ‖A − P‖)` for
`d = infDist P S`. -/
theorem side_bound (A B C P : E) {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hs : a + b + c = 1) (hP : P = a • A + b • B + c • C) (S : Set E)
    (hQ : AffineMap.lineMap B C (c / (b + c)) ∈ S) :
    infDist P S ≤ a * (infDist P S + ‖A - P‖) := by
  set Q := AffineMap.lineMap B C (c / (b + c)) with hQdef
  have hbc : 0 < b + c := by linarith
  have nbc := hbc.ne'
  have c1 : (b + c) * (1 - c / (b + c)) = b := by
    field_simp <;> ring
  have c2 : (b + c) * (c / (b + c)) = c := by
    field_simp
  have hQ' : (b + c) • Q = b • B + c • C := by
    rw [hQdef, AffineMap.lineMap_apply_module, smul_add, smul_smul, smul_smul, c1, c2]
  have hv : (b + c) • (P - Q) = a • (A - P) := by
    rw [smul_sub, hQ', hP, show b + c = 1 - a by linarith]
    module
  have hn : (b + c) * ‖P - Q‖ = a * ‖A - P‖ := by
    have := congrArg norm hv
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos hbc, abs_of_pos ha] using this
  have hdQ : infDist P S ≤ ‖P - Q‖ := (infDist_le_dist_of_mem hQ).trans_eq (dist_eq_norm P Q)
  have := mul_le_mul_of_nonneg_left hdQ hbc.le
  rw [show b + c = 1 - a by linarith] at this hn
  linarith

/-- `d ≤ a(d + x)` with `a ≥ 0` gives `d/(d + x) ≤ a`. -/
theorem ratio_le {d x a : ℝ} (hd : 0 ≤ d) (hx : 0 ≤ x) (ha : 0 ≤ a) (h : d ≤ a * (d + x)) :
    d / (d + x) ≤ a := by
  rcases (add_nonneg hd hx).eq_or_lt with h0 | h0
  · rw [← h0, div_zero]
    exact ha
  · rw [div_le_iff₀ h0]
    linarith

/-- **Erdős–Mordell with constant `3/2`** for arbitrary sets `Sᵢ` containing the two endpoints
of side `i` and the barycentric foot `Qᵢ`; lines and segments are both instances. -/
theorem erdos_mordell_sets (A1 A2 A3 P : E) {a1 a2 a3 : ℝ} (h1 : 0 < a1) (h2 : 0 < a2)
    (h3 : 0 < a3) (hs : a1 + a2 + a3 = 1) (hP : P = a1 • A1 + a2 • A2 + a3 • A3)
    (S1 S2 S3 : Set E)
    (hS1 : A2 ∈ S1 ∧ A3 ∈ S1 ∧ AffineMap.lineMap A2 A3 (a3 / (a2 + a3)) ∈ S1)
    (hS2 : A3 ∈ S2 ∧ A1 ∈ S2 ∧ AffineMap.lineMap A3 A1 (a1 / (a3 + a1)) ∈ S2)
    (hS3 : A1 ∈ S3 ∧ A2 ∈ S3 ∧ AffineMap.lineMap A1 A2 (a2 / (a1 + a2)) ∈ S3) :
    3 / 2 * (infDist P S1 + infDist P S2 + infDist P S3) ≤ ‖A1 - P‖ + ‖A2 - P‖ + ‖A3 - P‖ := by
  have hx : ∀ {S : Set E} {B : E}, B ∈ S → infDist P S ≤ ‖B - P‖ := fun hB =>
    (infDist_le_dist_of_mem hB).trans_eq (by rw [dist_comm, dist_eq_norm])
  have b1 := side_bound A1 A2 A3 P h1 h2 h3 hs hP S1 hS1.2.2
  have b2 := side_bound A2 A3 A1 P h2 h3 h1 (by linarith) (by rw [hP]; abel) S2 hS2.2.2
  have b3 := side_bound A3 A1 A2 P h3 h1 h2 (by linarith) (by rw [hP]; abel) S3 hS3.2.2
  have hphi := add_le_add (add_le_add (ratio_le infDist_nonneg (norm_nonneg _) h1.le b1)
    (ratio_le infDist_nonneg (norm_nonneg _) h2.le b2))
    (ratio_le infDist_nonneg (norm_nonneg _) h3.le b3)
  exact algebra _ _ _ _ _ _ infDist_nonneg infDist_nonneg infDist_nonneg (hx hS2.2.1)
    (hx hS3.1) (hx hS1.1) (hx hS3.2.1) (hx hS1.2.1) (hx hS2.1) (by linarith)

/-- `c/(b + c) ∈ [0, 1]` for positive `b, c`. -/
theorem frac_mem_Icc {b c : ℝ} (hb : 0 < b) (hc : 0 < c) : c / (b + c) ∈ Set.Icc 0 1 :=
  ⟨div_nonneg hc.le (by linarith), (div_le_one (by linarith)).2 (by linarith)⟩

/-- **The theorem, for side lines**, in any real normed space. -/
theorem erdos_mordell (A1 A2 A3 P : E) {a1 a2 a3 : ℝ} (h1 : 0 < a1) (h2 : 0 < a2)
    (h3 : 0 < a3) (hs : a1 + a2 + a3 = 1) (hP : P = a1 • A1 + a2 • A2 + a3 • A3) :
    3 / 2 * (infDist P (line[ℝ, A2, A3] : Set E) + infDist P (line[ℝ, A3, A1] : Set E)
      + infDist P (line[ℝ, A1, A2] : Set E)) ≤ ‖A1 - P‖ + ‖A2 - P‖ + ‖A3 - P‖ :=
  erdos_mordell_sets A1 A2 A3 P h1 h2 h3 hs hP _ _ _
    ⟨left_mem_affineSpan_pair .., right_mem_affineSpan_pair ..,
      AffineMap.lineMap_mem_affineSpan_pair _ _ _⟩
    ⟨left_mem_affineSpan_pair .., right_mem_affineSpan_pair ..,
      AffineMap.lineMap_mem_affineSpan_pair _ _ _⟩
    ⟨left_mem_affineSpan_pair .., right_mem_affineSpan_pair ..,
      AffineMap.lineMap_mem_affineSpan_pair _ _ _⟩

/-- **The theorem, for side segments** (the write-up's second assertion). -/
theorem erdos_mordell_segments (A1 A2 A3 P : E) {a1 a2 a3 : ℝ} (h1 : 0 < a1) (h2 : 0 < a2)
    (h3 : 0 < a3) (hs : a1 + a2 + a3 = 1) (hP : P = a1 • A1 + a2 • A2 + a3 • A3) :
    3 / 2 * (infDist P (segment ℝ A2 A3) + infDist P (segment ℝ A3 A1)
      + infDist P (segment ℝ A1 A2)) ≤ ‖A1 - P‖ + ‖A2 - P‖ + ‖A3 - P‖ :=
  erdos_mordell_sets A1 A2 A3 P h1 h2 h3 hs hP _ _ _
    ⟨left_mem_segment .., right_mem_segment .., lineMap_mem_segment (ht := frac_mem_Icc h2 h3) ..⟩
    ⟨left_mem_segment .., right_mem_segment .., lineMap_mem_segment (ht := frac_mem_Icc h3 h1) ..⟩
    ⟨left_mem_segment .., right_mem_segment .., lineMap_mem_segment (ht := frac_mem_Icc h1 h2) ..⟩

/-- **MathDB #341671 (Conjecture 1 of Petrović–Malešević–Banjac)**: in the taxicab plane, an
interior point's distances to the vertices sum to at least `3/2` times its distances to the side
lines. -/
theorem taxicab_erdos_mordell (A1 A2 A3 P : PiLp 1 (fun _ : Fin 2 => ℝ)) {a1 a2 a3 : ℝ}
    (h1 : 0 < a1) (h2 : 0 < a2) (h3 : 0 < a3) (hs : a1 + a2 + a3 = 1)
    (hP : P = a1 • A1 + a2 • A2 + a3 • A3) :
    3 / 2 * (infDist P (line[ℝ, A2, A3] : Set _) + infDist P (line[ℝ, A3, A1] : Set _)
      + infDist P (line[ℝ, A1, A2] : Set _)) ≤ ‖A1 - P‖ + ‖A2 - P‖ + ‖A3 - P‖ :=
  erdos_mordell A1 A2 A3 P h1 h2 h3 hs hP

end Principia.MathDB.P341671
