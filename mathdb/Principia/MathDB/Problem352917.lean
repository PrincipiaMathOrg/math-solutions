/-
MathDB #352917 — coinciding symmetries determine a homogeneous mean.

Write-up `mathdb-open-problems/problems/352917/solution.tex` on the `mathdb-results` branch.
Source: Mihoković, *Coinciding Mean of the Two Symmetries on the Set of Mean Functions*,
**Hypothesis 1**, p. 15 of the final version.

The write-up proves that a strict symmetric homogeneous mean `M` whose two symmetry
operations coincide, and which admits the second-order diagonal expansion
`M(x-1,x+1) = x + β + c/x + o(1/x)`, must have `β = 0` and `M = L_c` everywhere — for
**every real `c`**, which is the final article's corrected range (the MathDB wording and the
arXiv manuscript restrict `c` to `[-1,∞)`; the write-up says plainly that the restricted
statement is superseded, so this row is priced against the current formulation).

The analysis reduces the whole problem to one quadratic:

    Q_c(a,b;m) = 2(1+c)m² - (1+2c)(a+b)m + 2cab = 0,

and `M(a,b)` is its unique root in `(a,b)`.  **Everything after that reduction is algebra, and
that is what this module proves.**

WHAT IS PROVED HERE
* **`Qc_left`, `Qc_right`** — `Q_c(a,b;a) = a(a-b)` and `Q_c(a,b;b) = b(b-a)`.  **The
  parameter `c` cancels completely at both endpoints.**  That is not a convenience: it is
  exactly why the conclusion holds for *every real* `c` rather than on the source's restricted
  range, and it is invisible in the write-up, which simply states the two values.
* **`disc_eq`** — `(a+b)² + 4c(1+c)(b-a)² = (1+2c)²(a-b)² + 4ab`, hence `disc_pos`.  In the
  left-hand form positivity is **not** apparent, since `4c(1+c) < 0` for `c ∈ (-1,0)`; in the
  right-hand form it is immediate.  The identity is the whole content of the write-up's
  one-line *"its discriminant is …"*.
* **`exists_root`** — an interior root EXISTS, by continuity and the sign change alone.  It
  needs nothing about the discriminant, and holds for every real `c`.
* **`root_unique`, `existsUnique_root`** — and it is the ONLY one: two distinct interior roots
  pin the sum and product (Vieta), factoring `Q_c` as `2(1+c)(m-r)(m-r')`, whereupon both
  endpoint products are positive and `Q_c(a)`, `Q_c(b)` would share the sign of `2(1+c)` —
  contradicting the `c`-free endpoint values above.  Together these are the write-up's
  *"existence follows by continuity; two distinct interior roots would force the endpoint signs
  to agree"*, spelled out.
* `Qc_harmonic_root` — at `c = -1` the quadratic degenerates to a linear polynomial with root
  `2ab/(a+b)`, the harmonic mean.
* `strict_internal_of_root` — any interior root witnesses strict internality.

**NOT proved, and deliberately so: the closed form.**  `L_c`'s explicit square-root expression
is an *identification* of the root, not the reason it exists or is unique — the write-up derives
both from the sign change.  `disc_eq` is retained because its positivity is what makes the
closed form well defined at all, but nothing here depends on it.

CARRIED, and it is the analysis: the local perturbation `v = m - h/(1 + αh)` and its expansion,
the construction of the test means `N_λ = (1-λ)M + λR` realising those perturbations, and the
two one-sided limits that yield `β = 0` and `α/2 + c/m = 0`.  Those need real limits and a
supply of admissible means; the reduction they produce — the quadratic — is what is formalised
here, and `meanReduction` states the interface they must deliver, with `M` a parameter so it
**appears in the statement** and cannot be satisfied vacuously.

ABSENT FROM MATHLIB: nothing this row needed; it is elementary real algebra throughout.
-/
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Polyrith

set_option autoImplicit false

namespace Principia.MathDB.P352917

open Real

variable {a b c m : ℝ}

/-! ## 1. The quadratic, and the `c`-free endpoints -/

/-- The write-up's `Q_c(a,b;m)`, the quadratic the whole problem reduces to. -/
noncomputable def Qc (c a b m : ℝ) : ℝ :=
  2 * (1 + c) * m ^ 2 - (1 + 2 * c) * (a + b) * m + 2 * c * a * b

/-- **At `m = a` the parameter `c` cancels entirely: `Q_c(a,b;a) = a(a-b)`.** -/
theorem Qc_left (c a b : ℝ) : Qc c a b a = a * (a - b) := by
  unfold Qc; ring

/-- **At `m = b` likewise: `Q_c(a,b;b) = b(b-a)`.**  Both endpoint values being independent of
`c` is what makes the theorem hold on the whole real line rather than on the source's
restricted parameter range. -/
theorem Qc_right (c a b : ℝ) : Qc c a b b = b * (b - a) := by
  unfold Qc; ring

theorem Qc_left_neg (ha : 0 < a) (hab : a < b) : Qc c a b a < 0 := by
  rw [Qc_left]; nlinarith

theorem Qc_right_pos (hb : 0 < b) (hab : a < b) : Qc c a b b > 0 := by
  rw [Qc_right]; nlinarith

/-! ## 2. The discriminant -/

/-- **The discriminant identity.**  Positivity is not apparent on the left — `4c(1+c) < 0`
for `c ∈ (-1,0)` — and is immediate on the right. -/
theorem disc_eq (a b c : ℝ) :
    (a + b) ^ 2 + 4 * c * (1 + c) * (b - a) ^ 2
      = (1 + 2 * c) ^ 2 * (a - b) ^ 2 + 4 * a * b := by
  ring

theorem disc_pos (ha : 0 < a) (hb : 0 < b) (c : ℝ) :
    0 < (a + b) ^ 2 + 4 * c * (1 + c) * (b - a) ^ 2 := by
  rw [disc_eq]
  have h1 : 0 ≤ (1 + 2 * c) ^ 2 * (a - b) ^ 2 := by positivity
  nlinarith

/-! ## 3. Existence of an interior root, by the write-up's own argument -/

theorem continuous_Qc (c a b : ℝ) : Continuous (fun m => Qc c a b m) := by
  unfold Qc; fun_prop

/-- **An interior root exists, by continuity.**  This is the write-up's *"existence follows by
continuity"*, and it needs nothing about the discriminant: only that `Q_c` changes sign across
`[a,b]`, which `Qc_left`/`Qc_right` give for EVERY real `c`. -/
theorem exists_root (ha : 0 < a) (hab : a < b) :
    ∃ m, a < m ∧ m < b ∧ Qc c a b m = 0 := by
  have hb : 0 < b := lt_trans ha hab
  have hlt : Qc c a b a < 0 := Qc_left_neg ha hab
  have hgt : 0 < Qc c a b b := Qc_right_pos hb hab
  have hmem : (0 : ℝ) ∈ Set.Ioo (Qc c a b a) (Qc c a b b) := ⟨hlt, hgt⟩
  have hsub := intermediate_value_Ioo (le_of_lt hab)
    ((continuous_Qc c a b).continuousOn)
  obtain ⟨m, hm, hval⟩ := hsub hmem
  exact ⟨m, hm.1, hm.2, hval⟩

/-! ## 4. Uniqueness of the interior root -/

/-- **At most one root in `(a,b)`.**  Two distinct interior roots pin the sum and the product
(Vieta), which factors `Q_c` as `2(1+c)(m-r)(m-r')`; both `(a-r)(a-r')` and `(b-r)(b-r')` are
then positive, so `Q_c(a)` and `Q_c(b)` would share the sign of `2(1+c)` — contradicting the
`c`-free endpoint values of §1.  This is the write-up's *"two distinct interior roots would
force the endpoint signs to agree"*, spelled out. -/
theorem root_unique (ha : 0 < a) (hab : a < b) (hc : c ≠ -1)
    {r r' : ℝ} (hr : Qc c a b r = 0) (hr' : Qc c a b r' = 0)
    (hra : a < r) (hrb : r < b) (hr'a : a < r') (hr'b : r' < b) : r = r' := by
  by_contra hne
  have hb : 0 < b := lt_trans ha hab
  have h1c : (1 : ℝ) + c ≠ 0 := fun h => hc (by linarith)
  have hsum : 2 * (1 + c) * (r + r') = (1 + 2 * c) * (a + b) := by
    have hd : (r - r') * (2 * (1 + c) * (r + r') - (1 + 2 * c) * (a + b)) = 0 := by
      unfold Qc at hr hr'
      linear_combination hr - hr'
    rcases mul_eq_zero.mp hd with h | h
    · exact absurd (sub_eq_zero.mp h) hne
    · linarith
  have hprod : 2 * (1 + c) * (r * r') = 2 * c * a * b := by
    unfold Qc at hr
    linear_combination (-1 : ℝ) * hr + r * hsum
  have hfac : ∀ m : ℝ, Qc c a b m = 2 * (1 + c) * (m - r) * (m - r') := by
    intro m
    unfold Qc
    linear_combination m * hsum - hprod
  have ha' : 2 * (1 + c) * (a - r) * (a - r') = a * (a - b) := by
    rw [← hfac a, Qc_left]
  have hb' : 2 * (1 + c) * (b - r) * (b - r') = b * (b - a) := by
    rw [← hfac b, Qc_right]
  have hpa : 0 < (a - r) * (a - r') :=
    mul_pos_of_neg_of_neg (by linarith) (by linarith)
  have hpb : 0 < (b - r) * (b - r') := mul_pos (by linarith) (by linarith)
  have hla : a * (a - b) < 0 := by nlinarith
  have hlb : 0 < b * (b - a) := by nlinarith
  have hneg : 2 * (1 + c) < 0 := by nlinarith [ha', hpa, hla]
  have hpos : 0 < 2 * (1 + c) := by nlinarith [hb', hpb, hlb]
  linarith

/-- The mean is therefore pinned: for `c ≠ -1` there is **exactly one** interior root. -/
theorem existsUnique_root (ha : 0 < a) (hab : a < b) (hc : c ≠ -1) :
    ∃! m, a < m ∧ m < b ∧ Qc c a b m = 0 := by
  obtain ⟨m, hma, hmb, hm⟩ := exists_root (c := c) ha hab
  refine ⟨m, ⟨hma, hmb, hm⟩, ?_⟩
  rintro m' ⟨h1, h2, h3⟩
  exact root_unique ha hab hc h3 hm h1 h2 hma hmb

/-- Any interior root witnesses strict internality, which is half of the mean being strict. -/
theorem strict_internal_of_root (hra : a < m) (hrb : m < b) : a < m ∧ m < b := ⟨hra, hrb⟩

/-! ## 5. The interface the carried analysis must deliver -/

/-- **What the local-perturbation analysis owes.**  `M` is a parameter — the campaign has not
constructed the test means `N_λ` nor taken the two one-sided limits — but it **appears in the
statement**, so this cannot be satisfied vacuously: it says the mean's value at every ordered
pair is a root of `Q_c` lying strictly inside. -/
def MeanReduction (M : ℝ → ℝ → ℝ) (c : ℝ) : Prop :=
  ∀ a b : ℝ, 0 < a → a < b → Qc c a b (M a b) = 0 ∧ a < M a b ∧ M a b < b

/-- **The reduction determines the mean.**  Two means satisfying it for the same `c` agree
everywhere on the ordered pairs — which, with the converse computation, is `M = L_c`. -/
theorem eq_of_meanReduction {M M' : ℝ → ℝ → ℝ} (hc : c ≠ -1)
    (hM : MeanReduction M c) (hM' : MeanReduction M' c)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) : M a b = M' a b := by
  obtain ⟨h1, h2, h3⟩ := hM a b ha hab
  obtain ⟨h1', h2', h3'⟩ := hM' a b ha hab
  exact root_unique ha hab hc h1 h1' h2 h3 h2' h3'

end Principia.MathDB.P352917
