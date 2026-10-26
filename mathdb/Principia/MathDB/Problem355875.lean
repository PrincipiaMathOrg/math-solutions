import Mathlib

/-!
# MathDB #355875 — the derivative-polynomial combinations can share a positive zero

Write-up: `antoshashakov/Principia-Math-In-Progress`, branch `mathdb-results`,
`mathdb-open-problems/problems/355875/solution.tex`, refuting Conjecture 2.8 of Erdélyi, Rosenblatt
and Rosenblatt.  With `A₀(x) = x/(1+x²)^{3/2}`, `B₀(x) = 1/(1+x²)^{3/2}` and the numerators
`A₀^{(l)} = P_l/(1+x²)^{(2l+3)/2}`, `B₀^{(l)} = Q_l/(1+x²)^{(2l+3)/2}`, the conjecture asserts that
for real `γ₀, …, γ_L`, not all zero, the polynomials `F_γ = ∑ γ_l (1+x²)^{L−l} xˡ P_l` and
`G_γ = ∑ γ_l (1+x²)^{L−l} xˡ Q_l` have no common positive zero.

**What is refuted.**  `ERRConj` is the conjecture at `L = 2` only (a restriction).  The numerators
enter only through the identities they satisfy: any `P, Q` with
`iteratedDeriv l A₀ x = P l x / (1+x²)^{(2l+3)/2}` (and likewise for `B₀`) for `l ≤ 2` are admitted,
and these identities force them to be the source's `P_l, Q_l`.

**The witness (the write-up's).**  `P = (x, 1 − 2x², 6x³ − 9x)`, `Q = (1, −3x, 12x² − 3)`, proved to
be the derivative numerators with real powers (`idA0`–`idB2`, from `HasDerivAt.rpow_const`), and
`γ = (18, 30, 25)`: then `F_γ(1/2) = G_γ(1/2) = 0`.  Checked in SymPy
(`F_γ = 3x(4x²−1)(9x²−16)`, `G_γ = 3(4x²−1)(19x²−6)`).

**Absent:** the write-up's one-parameter family (every positive point is a common zero) and the
minimality in derivative order.
-/

namespace Principia.MathDB.P355875

open Finset

/-- `A₀(x) = x/(1+x²)^{3/2}`. -/
noncomputable def A0 (x : ℝ) : ℝ := x / (1 + x ^ 2) ^ ((3 : ℝ) / 2)

/-- `B₀(x) = 1/(1+x²)^{3/2}`. -/
noncomputable def B0 (x : ℝ) : ℝ := 1 / (1 + x ^ 2) ^ ((3 : ℝ) / 2)

/-- `∑_{l ≤ L} γ_l (1+x²)^{L−l} xˡ R_l(x)`. -/
noncomputable def comb (L : ℕ) (γ : ℕ → ℝ) (R : ℕ → ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ l ∈ range (L + 1), γ l * (1 + x ^ 2) ^ (L - l) * x ^ l * R l x

/-- Conjecture 2.8 of Erdélyi–Rosenblatt–Rosenblatt at `L = 2`. -/
def ERRConj : Prop :=
  ∀ P Q : ℕ → ℝ → ℝ,
    (∀ l ≤ 2, ∀ x, iteratedDeriv l A0 x = P l x / (1 + x ^ 2) ^ ((2 * l + 3 : ℝ) / 2)) →
    (∀ l ≤ 2, ∀ x, iteratedDeriv l B0 x = Q l x / (1 + x ^ 2) ^ ((2 * l + 3 : ℝ) / 2)) →
    ∀ γ : ℕ → ℝ, (∃ l ≤ 2, γ l ≠ 0) →
      ¬ ∃ x : ℝ, 0 < x ∧ comb 2 γ P x = 0 ∧ comb 2 γ Q x = 0

/-- The table of `P_l`. -/
def Pt : ℕ → ℝ → ℝ
  | 0, x => x
  | 1, x => 1 - 2 * x ^ 2
  | _, x => 6 * x ^ 3 - 9 * x

/-- The table of `Q_l`. -/
def Qt : ℕ → ℝ → ℝ
  | 0, _ => 1
  | 1, x => -3 * x
  | _, x => 12 * x ^ 2 - 3

/-- `γ = (18, 30, 25)`. -/
def gam : ℕ → ℝ := fun l => if l = 0 then 18 else if l = 1 then 30 else 25

theorem hw (x a : ℝ) : (1 + x ^ 2) ^ a = (1 + x ^ 2) * (1 + x ^ 2) ^ (a - 1) := by
  have ht : 0 < 1 + x ^ 2 := by positivity
  conv_lhs => rw [show a = 1 + (a - 1) by ring]
  rw [Real.rpow_add ht, Real.rpow_one]

theorem dv (c x a : ℝ) : c / (1 + x ^ 2) ^ a = c * (1 + x ^ 2) ^ (-a) := by
  rw [div_eq_mul_inv, Real.rpow_neg (by positivity)]

theorem hasDerivAt_w (p x : ℝ) :
    HasDerivAt (fun y => (1 + y ^ 2) ^ p) (2 * x * p * (1 + x ^ 2) ^ (p - 1)) x := by
  have h1 : HasDerivAt (fun y : ℝ => 1 + y ^ 2) (2 * x) x := by
    simpa using (hasDerivAt_pow 2 x).const_add 1
  exact h1.rpow_const (Or.inl (by positivity))

theorem hA0 : A0 = fun y => y * (1 + y ^ 2) ^ (-3 / 2 : ℝ) := by
  funext y
  rw [A0, dv, neg_div]

theorem hB0 : B0 = fun y => (1 + y ^ 2) ^ (-3 / 2 : ℝ) := by
  funext y
  rw [B0, dv, neg_div, one_mul]

theorem dA0 (x : ℝ) : HasDerivAt (fun y => y * (1 + y ^ 2) ^ (-3 / 2 : ℝ))
    ((1 - 2 * x ^ 2) * (1 + x ^ 2) ^ (-5 / 2 : ℝ)) x := by
  refine ((hasDerivAt_id' x).mul (hasDerivAt_w (-3 / 2) x)).congr_deriv ?_
  rw [hw x (-3 / 2), show (-3 / 2 : ℝ) - 1 = -5 / 2 by norm_num]
  ring

theorem dA1 (x : ℝ) : HasDerivAt (fun y => (1 - 2 * y ^ 2) * (1 + y ^ 2) ^ (-5 / 2 : ℝ))
    ((6 * x ^ 3 - 9 * x) * (1 + x ^ 2) ^ (-7 / 2 : ℝ)) x := by
  have hc : HasDerivAt (fun y : ℝ => 1 - 2 * y ^ 2) (-4 * x) x := by
    refine (((hasDerivAt_pow 2 x).const_mul 2).const_sub 1).congr_deriv ?_
    norm_num
    try ring
  refine (hc.mul (hasDerivAt_w (-5 / 2) x)).congr_deriv ?_
  rw [hw x (-5 / 2), show (-5 / 2 : ℝ) - 1 = -7 / 2 by norm_num]
  ring

theorem dB0 (x : ℝ) : HasDerivAt (fun y => (1 + y ^ 2) ^ (-3 / 2 : ℝ))
    ((-3 * x) * (1 + x ^ 2) ^ (-5 / 2 : ℝ)) x := by
  refine (hasDerivAt_w (-3 / 2) x).congr_deriv ?_
  rw [show (-3 / 2 : ℝ) - 1 = -5 / 2 by norm_num]
  ring

theorem dB1 (x : ℝ) : HasDerivAt (fun y => (-3 * y) * (1 + y ^ 2) ^ (-5 / 2 : ℝ))
    ((12 * x ^ 2 - 3) * (1 + x ^ 2) ^ (-7 / 2 : ℝ)) x := by
  have hc : HasDerivAt (fun y : ℝ => -3 * y) (-3) x := by
    simpa using (hasDerivAt_id' x).const_mul (-3 : ℝ)
  refine (hc.mul (hasDerivAt_w (-5 / 2) x)).congr_deriv ?_
  rw [hw x (-5 / 2), show (-5 / 2 : ℝ) - 1 = -7 / 2 by norm_num]
  ring

theorem idA0 (x : ℝ) : iteratedDeriv 0 A0 x = x / (1 + x ^ 2) ^ ((3 : ℝ) / 2) := by
  rw [iteratedDeriv_zero, A0]

theorem idA1 (x : ℝ) : iteratedDeriv 1 A0 x = (1 - 2 * x ^ 2) / (1 + x ^ 2) ^ ((5 : ℝ) / 2) := by
  rw [iteratedDeriv_one, hA0, (dA0 x).deriv, dv, neg_div]

theorem idA2 (x : ℝ) :
    iteratedDeriv 2 A0 x = (6 * x ^ 3 - 9 * x) / (1 + x ^ 2) ^ ((7 : ℝ) / 2) := by
  have hd : deriv (fun y : ℝ => y * (1 + y ^ 2) ^ (-3 / 2 : ℝ))
      = fun y : ℝ => (1 - 2 * y ^ 2) * (1 + y ^ 2) ^ (-5 / 2 : ℝ) :=
    funext fun y => (dA0 y).deriv
  rw [iteratedDeriv_succ, iteratedDeriv_one, hA0, hd, (dA1 x).deriv, dv, neg_div]

theorem idB0 (x : ℝ) : iteratedDeriv 0 B0 x = 1 / (1 + x ^ 2) ^ ((3 : ℝ) / 2) := by
  rw [iteratedDeriv_zero, B0]

theorem idB1 (x : ℝ) : iteratedDeriv 1 B0 x = (-3 * x) / (1 + x ^ 2) ^ ((5 : ℝ) / 2) := by
  rw [iteratedDeriv_one, hB0, (dB0 x).deriv, dv, neg_div]

theorem idB2 (x : ℝ) :
    iteratedDeriv 2 B0 x = (12 * x ^ 2 - 3) / (1 + x ^ 2) ^ ((7 : ℝ) / 2) := by
  have hd : deriv (fun y : ℝ => (1 + y ^ 2) ^ (-3 / 2 : ℝ))
      = fun y : ℝ => (-3 * y) * (1 + y ^ 2) ^ (-5 / 2 : ℝ) :=
    funext fun y => (dB0 y).deriv
  rw [iteratedDeriv_succ, iteratedDeriv_one, hB0, hd, (dB1 x).deriv, dv, neg_div]

theorem P_ok : ∀ l ≤ 2, ∀ x : ℝ,
    iteratedDeriv l A0 x = Pt l x / (1 + x ^ 2) ^ ((2 * l + 3 : ℝ) / 2) := by
  intro l hl x
  rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2) with rfl | rfl | rfl
  · rw [show ((2 * ((0 : ℕ) : ℝ) + 3) / 2) = (3 : ℝ) / 2 by norm_num]
    exact idA0 x
  · rw [show ((2 * ((1 : ℕ) : ℝ) + 3) / 2) = (5 : ℝ) / 2 by norm_num]
    exact idA1 x
  · rw [show ((2 * ((2 : ℕ) : ℝ) + 3) / 2) = (7 : ℝ) / 2 by norm_num]
    exact idA2 x

theorem Q_ok : ∀ l ≤ 2, ∀ x : ℝ,
    iteratedDeriv l B0 x = Qt l x / (1 + x ^ 2) ^ ((2 * l + 3 : ℝ) / 2) := by
  intro l hl x
  rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2) with rfl | rfl | rfl
  · rw [show ((2 * ((0 : ℕ) : ℝ) + 3) / 2) = (3 : ℝ) / 2 by norm_num]
    exact idB0 x
  · rw [show ((2 * ((1 : ℕ) : ℝ) + 3) / 2) = (5 : ℝ) / 2 by norm_num]
    exact idB1 x
  · rw [show ((2 * ((2 : ℕ) : ℝ) + 3) / 2) = (7 : ℝ) / 2 by norm_num]
    exact idB2 x

theorem F_half : comb 2 gam Pt (1 / 2) = 0 := by
  norm_num [comb, Finset.sum_range_succ, gam, Pt]

theorem G_half : comb 2 gam Qt (1 / 2) = 0 := by
  norm_num [comb, Finset.sum_range_succ, gam, Qt]

/-- **MathDB #355875: Conjecture 2.8 of Erdélyi–Rosenblatt–Rosenblatt is false** (at `L = 2`,
`γ = (18, 30, 25)`, common zero `1/2`). -/
theorem not_errConj : ¬ ERRConj := by
  intro h
  exact h Pt Qt P_ok Q_ok gam ⟨0, by norm_num, by simp [gam]⟩
    ⟨1 / 2, by norm_num, F_half, G_half⟩

end Principia.MathDB.P355875
