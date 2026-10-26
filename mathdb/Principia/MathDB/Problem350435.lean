import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

set_option autoImplicit false

/-!
# MathDB 350435 — the Laplace-transform threshold for `1/(1 + m s eˢ)`

Write-up: `mathdb-open-problems/problems/350435/solution.tex` on the `mathdb-results`
branch of `antoshashakov/Principia-Math-In-Progress`.  It resolves **Conjecture 1** of
Kesidis, Konstantopoulos and Zazanis (p. 18):

  `L_m(s) = 1/(1 + m s eˢ)`, `s ≥ 0`, is the Laplace transform of a probability
  distribution **iff** `m = 0` or `m ≥ e`.

The source's probabilistic construction already gave the sufficient range; the write-up
supplies the missing **necessity** and a direct construction for sufficiency.

## Necessity, and where its content sits

If `L_m` is such a transform then `X ≥ 0` a.s., every `(-1)ⁿ L_m⁽ⁿ⁾ ≥ 0`, and Pringsheim's
theorem forces the Taylor series of `F(z) = L_m(-z) = 1/(1 - m z e^{-z})` at `0` to have
**nonnegative** coefficients, `a₀ = 1`, `a₁ = m`, and **infinite radius** — so it
represents `F` on all of `[0, ∞)`.  That is carried (`Setup.hsum`).

Everything after it is elementary and is proved here:

* `mul_exp_neg_le` — `t e^{-t} ≤ 1/e` for **every** real `t`, from `x + 1 ≤ eˣ` at
  `x = t - 1`.  No sign hypothesis is needed.
* `Ffun_le` — hence `1 - m t e^{-t} ≥ 1 - m/e > 0` and `F(t) ≤ 1/(1 - m/e)`
  **uniformly in `t`**.
* `two_terms_le` — nonnegative coefficients give `1 + m t ≤ F(t)`, which is unbounded.
* `Setup.absurd_at` — the contradiction at the **explicit** point
  `t₀ = 1/(m(1 - m/e))`, where `1 + m t₀ = 1 + 1/(1 - m/e)` overshoots the uniform bound
  by exactly `1`, with slack independent of `m`.

## Sufficiency

* `lambda_exists` — for `m ≥ e` there is `λ ∈ (0,1]` with `e^λ/λ = m`, by the
  intermediate value theorem on `[1/m, 1]`: `g 1 = e ≤ m ≤ m·e^{1/m} = g (1/m)`.
* `denom_identity` — `1 - λ(1 - e^{-(λ+s)})/(λ+s) = (s + λ e^{-(λ+s)})/(λ+s)`, the step
  that sums the geometric series for the random sum.
* `Witness.transform_eq_L` — the source's `T = 1 + Z + ∑_{i≤J} Yᵢ` has transform
  `λ e^{-(λ+s)}/(s + λ e^{-(λ+s)})`, and **that equals `L_m(s)`** with `m = e^λ/λ`.
  The construction of `T` is carried; the identity is proved.

## Scope

`Campaigns/MathDB-Formalization/verify_350435.py` checks every bound here, and
independently confirms the write-up's scope claim by formal series inversion: for `m < e`
some Taylor coefficient of `F` really is negative (`n = 2` at `m = 1/2`, `n = 4` at
`m = 2`), while for `m ≥ e` the first 31 are all nonnegative.
-/

namespace Principia.MathDB.P350435

open Real Set

/-- `L_m(s) = 1/(1 + m s eˢ)`, the function in the conjecture. -/
noncomputable def L (m s : ℝ) : ℝ := 1 / (1 + m * s * exp s)

/-- `F(t) = L_m(-t) = 1/(1 - m t e^{-t})`, the germ Pringsheim is applied to. -/
noncomputable def Ffun (m t : ℝ) : ℝ := 1 / (1 - m * t * exp (-t))

/-! ## The elementary inequality -/

/-- **`t e^{-t} ≤ 1/e`**, for every real `t`, from `x + 1 ≤ eˣ` at `x = t - 1`.
No sign hypothesis is needed: for `t < 0` the left side is already negative. -/
theorem mul_exp_neg_le (t : ℝ) : t * exp (-t) ≤ 1 / exp 1 := by
  have het : 0 < exp t := Real.exp_pos t
  have he1 : 0 < exp 1 := Real.exp_pos 1
  have hsplit : exp (t - 1) = exp t / exp 1 := Real.exp_sub t 1
  have h : t * exp 1 ≤ exp t := by
    have h1 := Real.add_one_le_exp (t - 1)
    rw [hsplit, le_div_iff₀ he1] at h1
    have h2 : (t - 1 + 1) * exp 1 = t * exp 1 := by ring
    linarith [h1, h2.le, h2.ge]
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ het he1]
  linarith

theorem one_sub_div_pos {m : ℝ} (hme : m < exp 1) : 0 < 1 - m / exp 1 := by
  have he1 : 0 < exp 1 := Real.exp_pos 1
  rw [sub_pos, div_lt_one he1]
  exact hme

/-- The denominator of `F` is bounded below **uniformly in `t`**. -/
theorem denom_ge {m : ℝ} (hm : 0 ≤ m) (t : ℝ) :
    1 - m / exp 1 ≤ 1 - m * t * exp (-t) := by
  have h := mul_exp_neg_le t
  have h2 : m * (t * exp (-t)) ≤ m * (1 / exp 1) := mul_le_mul_of_nonneg_left h hm
  have h3 : m * (1 / exp 1) = m / exp 1 := by ring
  nlinarith [h2, h3.le, h3.ge]

theorem denom_pos {m : ℝ} (hm : 0 ≤ m) (hme : m < exp 1) (t : ℝ) :
    0 < 1 - m * t * exp (-t) :=
  lt_of_lt_of_le (one_sub_div_pos hme) (denom_ge hm t)

/-- **`F(t) ≤ 1/(1 - m/e)` uniformly in `t`** — the bound the contradiction contradicts. -/
theorem Ffun_le {m : ℝ} (hm : 0 ≤ m) (hme : m < exp 1) (t : ℝ) :
    Ffun m t ≤ 1 / (1 - m / exp 1) :=
  one_div_le_one_div_of_le (one_sub_div_pos hme) (denom_ge hm t)

theorem Ffun_pos {m : ℝ} (hm : 0 ≤ m) (hme : m < exp 1) (t : ℝ) : 0 < Ffun m t :=
  div_pos one_pos (denom_pos hm hme t)

/-! ## The carried half, and the contradiction -/

/-- What complete monotonicity and Pringsheim's theorem deliver. -/
structure Setup where
  m : ℝ
  hm0 : 0 < m
  hme : m < exp 1
  /-- the Taylor coefficients of `F` at `0` -/
  a : ℕ → ℝ
  /-- **CARRIED** (complete monotonicity of the transform): they are nonnegative. -/
  ha : ∀ n, 0 ≤ a n
  ha0 : a 0 = 1
  ha1 : a 1 = m
  /-- **CARRIED** (Pringsheim: the radius cannot be finite, its positive endpoint being
  a point of holomorphy): the series represents `F` on the whole of `[0, ∞)`. -/
  hsum : ∀ t : ℝ, 0 ≤ t → HasSum (fun n => a n * t ^ n) (Ffun m t)

namespace Setup

/-- Keeping only the first two terms: `1 + m t ≤ F(t)`.  NOTE the explicit `S` binder:
`absurd_at` below concludes `False`, whose statement mentions no `Setup`, so a section
`variable` would be silently dropped from it. -/
theorem two_terms_le (S : Setup) {t : ℝ} (ht : 0 ≤ t) : 1 + S.m * t ≤ Ffun S.m t := by
  have hs := S.hsum t ht
  have hnn : ∀ n ∉ Finset.range 2, 0 ≤ S.a n * t ^ n := fun n _ =>
    mul_nonneg (S.ha n) (pow_nonneg ht n)
  have h := sum_le_hasSum (Finset.range 2) hnn hs
  rw [Finset.sum_range_succ, Finset.sum_range_one, S.ha0, S.ha1] at h
  norm_num at h
  linarith

/-- **The contradiction, at an explicit point.**  At `t₀ = 1/(m(1 - m/e))` the two-term
lower bound is `1 + 1/(1 - m/e)`, overshooting the uniform upper bound by exactly `1`. -/
theorem absurd_at (S : Setup) : False := by
  have he1 : 0 < exp 1 := Real.exp_pos 1
  have he1ne : exp 1 ≠ 0 := he1.ne'
  have hc : 0 < 1 - S.m / exp 1 := one_sub_div_pos S.hme
  have hcne : 1 - S.m / exp 1 ≠ 0 := hc.ne'
  have hm0 := S.hm0
  have hmne : S.m ≠ 0 := hm0.ne'
  have hprod : 0 < S.m * (1 - S.m / exp 1) := mul_pos hm0 hc
  have ht₀nonneg : (0 : ℝ) ≤ 1 / (S.m * (1 - S.m / exp 1)) :=
    (div_pos one_pos hprod).le
  have hval : 1 + S.m * (1 / (S.m * (1 - S.m / exp 1))) = 1 + 1 / (1 - S.m / exp 1) := by
    field_simp
  have hlow := S.two_terms_le ht₀nonneg
  have hhigh := Ffun_le S.hm0.le S.hme (1 / (S.m * (1 - S.m / exp 1)))
  rw [hval] at hlow
  have hcap : 0 < 1 / (1 - S.m / exp 1) := by positivity
  linarith

end Setup

/-- **NECESSITY.**  No `m ∈ (0, e)` admits the nonnegative-coefficient expansion that a
Laplace transform of a probability distribution would force. -/
theorem necessity {m : ℝ} (hm0 : 0 < m) (hme : m < exp 1) (a : ℕ → ℝ)
    (ha : ∀ n, 0 ≤ a n) (ha0 : a 0 = 1) (ha1 : a 1 = m)
    (hsum : ∀ t : ℝ, 0 ≤ t → HasSum (fun n => a n * t ^ n) (Ffun m t)) : False :=
  Setup.absurd_at ⟨m, hm0, hme, a, ha, ha0, ha1, hsum⟩

/-! ## Sufficiency -/

/-- `g λ = e^λ / λ`, the parameter map. -/
noncomputable def g (l : ℝ) : ℝ := exp l / l

theorem g_one : g 1 = exp 1 := by simp [g]

theorem g_continuousOn {a b : ℝ} (ha : 0 < a) : ContinuousOn g (Icc a b) := by
  refine ContinuousOn.div (Real.continuous_exp.continuousOn) continuousOn_id ?_
  intro x hx
  exact ne_of_gt (lt_of_lt_of_le ha hx.1)

/-- **`λ` exists**: for `m ≥ e` some `λ ∈ (0,1]` has `e^λ/λ = m`.  The bracket is
`[1/m, 1]`, where `g 1 = e ≤ m` and `g (1/m) = m·e^{1/m} ≥ m`. -/
theorem lambda_exists {m : ℝ} (hm : exp 1 ≤ m) : ∃ l : ℝ, 0 < l ∧ l ≤ 1 ∧ g l = m := by
  have he1 : (1 : ℝ) < exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hm1 : 1 < m := lt_of_lt_of_le he1 hm
  have hm0 : 0 < m := lt_trans zero_lt_one hm1
  have hinv0 : 0 < 1 / m := by positivity
  have hinv1 : 1 / m ≤ 1 := by
    rw [div_le_one hm0]; linarith
  have hglo : m ≤ g (1 / m) := by
    have h1 : (1 : ℝ) ≤ exp (1 / m) := by
      have h2 := Real.add_one_le_exp (1 / m)
      linarith [hinv0]
    have h3 : g (1 / m) = exp (1 / m) * m := by
      rw [g]
      field_simp
    rw [h3]
    nlinarith [hm0, h1]
  have hghi : g 1 ≤ m := by rw [g_one]; exact hm
  have hsub := intermediate_value_Icc' hinv1 (g_continuousOn hinv0)
  have hmem : m ∈ Icc (g 1) (g (1 / m)) := ⟨hghi, hglo⟩
  obtain ⟨l, hl, hgl⟩ := hsub hmem
  exact ⟨l, lt_of_lt_of_le hinv0 hl.1, hl.2, hgl⟩

/-- The step that sums the geometric series for the random sum:
`1 - (1-p)φ(s) = (s + λ e^{-(λ+s)})/(λ+s)`. -/
theorem denom_identity {l s : ℝ} (hls : l + s ≠ 0) :
    1 - l * (1 - exp (-(l + s))) / (l + s)
      = (s + l * exp (-(l + s))) / (l + s) := by
  field_simp
  ring

/-- The carried probabilistic construction. -/
structure Witness where
  l : ℝ
  hl0 : 0 < l
  hl1 : l ≤ 1
  /-- the Laplace transform of the source's `T = 1 + Z + ∑_{i ≤ J} Yᵢ` -/
  transform : ℝ → ℝ
  /-- **CARRIED**: `T` is a finite nonnegative random variable and independence gives
  its transform this product form, with `p = e^{-λ}` and
  `φ(s) = λ(1 - e^{-(λ+s)})/((λ+s)(1-p))`. -/
  htrans : ∀ s : ℝ, 0 ≤ s →
    transform s = exp (-s) * (l / (l + s))
      * (exp (-l) / (1 - l * (1 - exp (-(l + s))) / (l + s)))

namespace Witness

variable (Wt : Witness)

theorem l_add_s_pos {s : ℝ} (hs : 0 ≤ s) : 0 < Wt.l + s := by
  linarith [Wt.hl0]

/-- **The transform of the construction is `L_m` with `m = e^λ/λ`.** -/
theorem transform_eq_L {s : ℝ} (hs : 0 ≤ s) : Wt.transform s = L (g Wt.l) s := by
  have hls : 0 < Wt.l + s := Wt.l_add_s_pos hs
  have hl0 := Wt.hl0
  have hel : 0 < exp Wt.l := Real.exp_pos _
  have hes : 0 < exp s := Real.exp_pos _
  have hkey : 0 < s + Wt.l * exp (-(Wt.l + s)) := by
    have : 0 < Wt.l * exp (-(Wt.l + s)) := by positivity
    linarith
  rw [Wt.htrans s hs, denom_identity hls.ne']
  rw [L, g]
  rw [Real.exp_neg, Real.exp_neg, Real.exp_neg, Real.exp_add]
  have hne : s * (exp Wt.l * exp s) + Wt.l ≠ 0 := by
    have h1 : 0 ≤ s * (exp Wt.l * exp s) := by positivity
    linarith
  field_simp
  ring

end Witness

/-- **SUFFICIENCY**, in the form the construction delivers it: for every `m ≥ e` there
is a `λ ∈ (0,1]` with `e^λ/λ = m`, and any witness built at that `λ` has transform
`L_m` on `[0, ∞)`. -/
theorem sufficiency {m : ℝ} (hm : exp 1 ≤ m) :
    ∃ l : ℝ, 0 < l ∧ l ≤ 1 ∧ g l = m ∧
      ∀ Wt : Witness, Wt.l = l → ∀ s : ℝ, 0 ≤ s → Wt.transform s = L m s := by
  obtain ⟨l, hl0, hl1, hgl⟩ := lambda_exists hm
  refine ⟨l, hl0, hl1, hgl, fun Wt hWl s hs => ?_⟩
  rw [Wt.transform_eq_L hs, hWl, hgl]

/-- The endpoint `m = e` is included, at `λ = 1`. -/
theorem endpoint : g 1 = exp 1 := g_one

end Principia.MathDB.P350435
