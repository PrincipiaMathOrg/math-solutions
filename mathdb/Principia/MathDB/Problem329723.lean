import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

/-!
# MathDB 329723 — the Meijer-function zero-count conjecture is false

Write-up: `mathdb-open-problems/problems/329723/solution.tex` on the `mathdb-results`
branch of `antoshashakov/Principia-Math-In-Progress`, "A counterexample to the
Meijer-function zero-count conjecture".  It refutes **Conjecture 1** of Karp and
Prilepkina: for `aᵢ ≥ 0` with `∑ᵢ (bᵢ - aᵢ) > 0`, the number of zeros of
`G^{p,0}_{p,p}(x ∣ b/a)` in `(0,1)` does not exceed the number of zeros there of
`v t = ∑ᵢ (t^{aᵢ} - t^{bᵢ})`.

## The witness

`a = (1, 1999/1000, 3099/1000, 3447/1000)`, `b = (5, 999/1000, 2099/1000, 2447/1000)`;
all positive, `∑ (bᵢ - aᵢ) = 1 > 0`.  Every `bᵢ - aᵢ` is an **integer**, which is why the
gamma recurrence collapses the Mellin multiplier to a rational function and the Meijer
function to a polynomial on `(0,1)`:

  `G x = x · Fc x / 6·10⁹`,
  `Fc x = 8859711253x³ - 2991012759x² + 132891759x - 1590253`.

## What is proved here

**The Meijer side, completely.**  `Fc` takes the four exact rational values
`Fc 0 = -1590253`, `Fc (1/40) = 69823293/64000`, `Fc (3/100) = -56199509269/10⁶`,
`Fc (3/10) = 8298330221/1000`, whose signs alternate; three applications of the
intermediate value theorem give three roots in disjoint subintervals of `(0,1)`, hence
distinct.  Since `x > 0` on `(0,1)`, these are zeros of `G` too.

## What is carried

Two things, both from the source:

* `G_eq`, the Mellin/gamma identification of the Meijer function with `x·Fc x/6·10⁹`;
* `v_le_one`, that `v` has **at most one** zero in `(0,1)`.

The second is worth a word.  Substituting `u = t^{1/1000}` gives
`v t = u^999 (1 - u^1000) q u` with
`q u = -1 + u + u^1001 - u^1100 - u^1448 + u^2001 + u^3001`, and the source certifies the
count by six Vincent/Budan substitutions whose coefficient sign strings have degree 3001.
That is not formalisable here — `native_decide` is banned and each polynomial has 3002
integer coefficients.  **Nor can it be replaced by a monotonicity argument**:
`Campaigns/MathDB-Formalization/verify_329723.py` finds that on `(99/100, 1)` the function
`q` rises to a local maximum of about `-1.7·10⁻⁵`, *just* below zero, and turns back down
before finally crossing.  Two extra roots are that close.  The heavy certificate is not
overkill.

The Python check does establish, exactly, that `q < 0` on `(0, 99/100]` — since each
positive high-degree term is at most `(99/100)^1001` there, so
`q ≤ -1/100 + 3(99/100)^1001 < 0` — and verifies the factorisation of `v` symbolically.

## The weakest reading

`Conj` says: if `G` has two distinct zeros in `(0,1)`, so does `v`.  That is the `≥ 2`
instance of "count `G` ≤ count `v`", and is implied by it; refuting it refutes the
conjecture.  Both carried facts are used — `v_le_one` supplies the contradiction's other
half, so neither hypothesis is decoration.
-/

namespace Principia.MathDB.P329723

open Set

/-- The cubic the Meijer function reduces to on `(0,1)`. -/
noncomputable def Fc (x : ℝ) : ℝ :=
  8859711253 * x ^ 3 - 2991012759 * x ^ 2 + 132891759 * x - 1590253

theorem Fc_continuous : Continuous Fc := by unfold Fc; fun_prop

theorem Fc_zero : Fc 0 = -1590253 := by unfold Fc; norm_num

theorem Fc_p1 : Fc (1 / 40) = 69823293 / 64000 := by unfold Fc; norm_num

theorem Fc_p2 : Fc (3 / 100) = -56199509269 / 1000000 := by unfold Fc; norm_num

theorem Fc_p3 : Fc (3 / 10) = 8298330221 / 1000 := by unfold Fc; norm_num

/-! ## Three roots, by three sign changes -/

theorem root_one : ∃ x ∈ Ioo (0 : ℝ) (1 / 40), Fc x = 0 := by
  have h : (0 : ℝ) ∈ Ioo (Fc 0) (Fc (1 / 40)) := by
    rw [Fc_zero, Fc_p1]; constructor <;> norm_num
  have hsub := intermediate_value_Ioo (by norm_num : (0 : ℝ) ≤ 1 / 40)
    Fc_continuous.continuousOn
  obtain ⟨x, hx, hfx⟩ := hsub h
  exact ⟨x, hx, hfx⟩

theorem root_two : ∃ x ∈ Ioo (1 / 40 : ℝ) (3 / 100), Fc x = 0 := by
  have h : (0 : ℝ) ∈ Ioo (Fc (3 / 100)) (Fc (1 / 40)) := by
    rw [Fc_p1, Fc_p2]; constructor <;> norm_num
  have hsub := intermediate_value_Ioo' (by norm_num : (1 / 40 : ℝ) ≤ 3 / 100)
    Fc_continuous.continuousOn
  obtain ⟨x, hx, hfx⟩ := hsub h
  exact ⟨x, hx, hfx⟩

theorem root_three : ∃ x ∈ Ioo (3 / 100 : ℝ) (3 / 10), Fc x = 0 := by
  have h : (0 : ℝ) ∈ Ioo (Fc (3 / 100)) (Fc (3 / 10)) := by
    rw [Fc_p2, Fc_p3]; constructor <;> norm_num
  have hsub := intermediate_value_Ioo (by norm_num : (3 / 100 : ℝ) ≤ 3 / 10)
    Fc_continuous.continuousOn
  obtain ⟨x, hx, hfx⟩ := hsub h
  exact ⟨x, hx, hfx⟩

/-- **Three** distinct zeros of `Fc` in `(0,1)`, separated by the sign-change points —
the source's count.  Degree `3` forbids a fourth. -/
theorem three_distinct_roots :
    ∃ x ∈ Ioo (0 : ℝ) 1, ∃ y ∈ Ioo (0 : ℝ) 1, ∃ z ∈ Ioo (0 : ℝ) 1,
      Fc x = 0 ∧ Fc y = 0 ∧ Fc z = 0 ∧ x < y ∧ y < z := by
  obtain ⟨x, hx, hfx⟩ := root_one
  obtain ⟨y, hy, hfy⟩ := root_two
  obtain ⟨z, hz, hfz⟩ := root_three
  exact ⟨x, ⟨hx.1, by linarith [hx.2]⟩, y, ⟨by linarith [hy.1], by linarith [hy.2]⟩,
    z, ⟨by linarith [hz.1], by linarith [hz.2]⟩, hfx, hfy, hfz,
    by linarith [hx.2, hy.1], by linarith [hy.2, hz.1]⟩

/-- Two of them suffice for the refutation. -/
theorem two_distinct_roots :
    ∃ x ∈ Ioo (0 : ℝ) 1, ∃ y ∈ Ioo (0 : ℝ) 1, Fc x = 0 ∧ Fc y = 0 ∧ x ≠ y := by
  obtain ⟨x, hx, y, _, z, hz, hfx, _, hfz, hxy, hyz⟩ := three_distinct_roots
  exact ⟨x, hx, z, hz, hfx, hfz, by linarith⟩

/-! ## The carried half -/

/-- The two facts taken from the source. -/
structure Setup where
  G : ℝ → ℝ
  /-- The gamma recurrence plus Mellin inversion. -/
  G_eq : ∀ x ∈ Ioo (0 : ℝ) 1, G x = x * Fc x / 6000000000
  v : ℝ → ℝ
  /-- The degree-3001 Descartes certificate: `v` has at most one zero in `(0,1)`. -/
  v_le_one : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ y ∈ Ioo (0 : ℝ) 1, v x = 0 → v y = 0 → x = y

namespace Setup

variable (S : Setup)

theorem G_eq_zero_iff {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : S.G x = 0 ↔ Fc x = 0 := by
  rw [S.G_eq x hx, div_eq_zero_iff, mul_eq_zero]
  constructor
  · rintro (h | h)
    · rcases h with h | h
      · exact absurd h (ne_of_gt hx.1)
      · exact h
    · norm_num at h
  · intro h; exact Or.inl (Or.inr h)

/-- `G` really does have two distinct zeros in `(0,1)`. -/
theorem G_two_zeros :
    ∃ x ∈ Ioo (0 : ℝ) 1, ∃ y ∈ Ioo (0 : ℝ) 1, S.G x = 0 ∧ S.G y = 0 ∧ x ≠ y := by
  obtain ⟨x, hx, y, hy, hfx, hfy, hne⟩ := two_distinct_roots
  exact ⟨x, hx, y, hy, (S.G_eq_zero_iff hx).mpr hfx, (S.G_eq_zero_iff hy).mpr hfy, hne⟩

end Setup

/-! ## The refutation -/

/-- Karp–Prilepkina Conjecture 1, in the weakest reading the witness kills: if `G` has two
distinct zeros in `(0,1)`, then so does `v`.  Implied by "count `G` ≤ count `v`". -/
def Conj (S : Setup) : Prop :=
  (∃ x ∈ Ioo (0 : ℝ) 1, ∃ y ∈ Ioo (0 : ℝ) 1, S.G x = 0 ∧ S.G y = 0 ∧ x ≠ y) →
    ∃ a ∈ Ioo (0 : ℝ) 1, ∃ b ∈ Ioo (0 : ℝ) 1, S.v a = 0 ∧ S.v b = 0 ∧ a ≠ b

/-- **Conjecture 1 is false.** -/
theorem not_conj (S : Setup) : ¬ Conj S := by
  intro h
  obtain ⟨a, ha, b, hb, hva, hvb, hne⟩ := h S.G_two_zeros
  exact hne (S.v_le_one a ha b hb hva hvb)

end Principia.MathDB.P329723
