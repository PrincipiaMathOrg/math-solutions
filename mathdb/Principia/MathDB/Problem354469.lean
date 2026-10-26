import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Tactic

/-!
# MathDB 354469 — coinciding transition attractors need not attract at the threshold

Write-up: `mathdb-open-problems/problems/354469/solution.tex` on the `mathdb-results`
branch of `antoshashakov/Principia-Math-In-Progress`.  It refutes **Conjecture 6.1** of
K. Leśniak, N. Snigireva, F. Strobin and A. Vince, *Transition phenomena for the attractor
of an iterated function system*, Nonlinearity **35** (2022), 5396–5426, p. 5425.

## The conjecture and what is refuted

Conjecture 6.1's conclusion is a **conjunction**: under (H1)–(H3), equality of the lower
transition attractor with one upper transition attractor forces

1. uniqueness of the upper transition attractor, **and**
2. attraction by the terminal IFS `F₁`.

In the witness below, **conclusion 1 holds** and **conclusion 2 fails**.  So the module
refutes the *conjunction*, which is all that is needed and all that is claimed:
`not_conj61` takes the uniqueness half as an opaque `Prop` and discards it, making it
syntactically impossible to read this as a refutation of uniqueness.

## The witness

On `ℝ`, with `r t = (1+t)/2`:

  `F_t = { x ↦ r t · x , x ↦ (r t / 2) · x }`,  `0 ≤ t ≤ 1`.

For `t < 1` both maps are Lipschitz with constant `r t < 1` and share the unique fixed
point `0`, so (H1)–(H3) hold and `{0}` attracts from every bounded set
(`attracts_of_lt_one`).  At `t = 1`, `r 1 = 1`, so the first map is the **identity**:
`mem_iter_one` shows `x ∈ (step 1)^[n] {x}` for every `n`, so the iterates of `{x}` never
enter a ball of radius `|x|` and no open neighbourhood of `0` is a basin.

## The weakest reading

`AttractsFrom` asks only that the iterates **eventually lie in every ball about `0`**.
Hausdorff convergence of `F₁ⁿ(K)` to `{0}` implies this, so refuting it refutes the
source's (stronger) Hausdorff-convergence notion a fortiori — and it avoids needing
`Metric.hausdorffDist` at all.

## A numerical fact worth recording

`Campaigns/MathDB-Formalization/verify_354469.py` checks the write-up's closed forms
`F_tⁿ(K) = ⋃_{k≤n} r tⁿ 2^{-k} K` and `h(F_tⁿ(K),{0}) = r tⁿ · max|K|` by direct set
iteration in exact rationals.  A first version of that check asserted a FIXED iterate count
for every `t < 1` and failed at `t = 3/4`, because `r t → 1` as `t → 1`: attraction holds
for each `t < 1` but **not uniformly**, which is exactly the phenomenon the example is
about.  The check now quantifies `∃ n` per `t`, and records that at `t = 1` no `n` works.
-/

namespace Principia.MathDB.P354469

open Set

/-- `r t = (1+t)/2`: the Lipschitz constant of the family, `< 1` exactly for `t < 1`. -/
noncomputable def r (t : ℝ) : ℝ := (1 + t) / 2

/-- One application of the IFS `F_t = {x ↦ r t · x, x ↦ (r t / 2) · x}`. -/
def step (t : ℝ) (S : Set ℝ) : Set ℝ :=
  (fun x => r t * x) '' S ∪ (fun x => (r t / 2) * x) '' S

/-- Attraction of `{0}` from `K`, in the weakest reading Hausdorff convergence implies. -/
def AttractsFrom (t : ℝ) (K : Set ℝ) : Prop :=
  ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, (step t)^[n] K ⊆ Metric.ball 0 ε

/-! ## The hypotheses (H1)–(H3) hold for this family -/

theorem r_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ r t := by
  unfold r; linarith

/-- (H2): the Lipschitz constant is below one exactly for `t < 1`. -/
theorem H2_lt_one {t : ℝ} (ht : t < 1) : r t < 1 := by
  unfold r; linarith

theorem r_one : r 1 = 1 := by unfold r; norm_num

/-- (H1): each map depends continuously on the parameter, at every point. -/
theorem H1_continuous (x : ℝ) :
    Continuous (fun t : ℝ => r t * x) ∧ Continuous (fun t : ℝ => (r t / 2) * x) := by
  constructor <;> · unfold r; fun_prop

/-- (H2), pointwise: both maps are Lipschitz with constant `r t`. -/
theorem H2_lipschitz (t x y : ℝ) (ht : 0 ≤ t) :
    |r t * x - r t * y| ≤ r t * |x - y| ∧
      |(r t / 2) * x - (r t / 2) * y| ≤ r t * |x - y| := by
  have h0 : 0 ≤ r t := r_nonneg ht
  constructor
  · rw [← mul_sub, abs_mul, abs_of_nonneg h0]
  · rw [← mul_sub, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ r t / 2)]
    nlinarith [abs_nonneg (x - y)]

/-- (H3): both maps fix `0` for every parameter, so the limit of fixed points is `0`. -/
theorem H3_fixed (t : ℝ) : r t * 0 = 0 ∧ (r t / 2) * 0 = 0 := by
  constructor <;> ring

/-! ## The exact decay bound -/

theorem step_bound {t B : ℝ} (ht : 0 ≤ r t) {S : Set ℝ} (hS : ∀ x ∈ S, |x| ≤ B) :
    ∀ y ∈ step t S, |y| ≤ r t * B := by
  rintro y (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
  · rw [abs_mul, abs_of_nonneg ht]
    exact mul_le_mul_of_nonneg_left (hS x hx) ht
  · have hB : 0 ≤ B := le_trans (abs_nonneg x) (hS x hx)
    rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ r t / 2)]
    nlinarith [abs_nonneg x, hS x hx]

theorem iter_bound {t M : ℝ} (ht : 0 ≤ r t) {K : Set ℝ} (hK : ∀ x ∈ K, |x| ≤ M) :
    ∀ n : ℕ, ∀ y ∈ (step t)^[n] K, |y| ≤ r t ^ n * M := by
  intro n
  induction n with
  | zero => simpa using hK
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      intro y hy
      have h := step_bound ht ih y hy
      calc |y| ≤ r t * (r t ^ n * M) := h
        _ = r t ^ (n + 1) * M := by ring

/-- For every `t < 1` the singleton `{0}` attracts from every bounded set. -/
theorem attracts_of_lt_one {t M : ℝ} (h0 : 0 ≤ t) (h1 : t < 1) {K : Set ℝ}
    (hK : ∀ x ∈ K, |x| ≤ M) (hM : 0 ≤ M) : AttractsFrom t K := by
  intro ε hε
  have hr0 : 0 ≤ r t := r_nonneg h0
  have hr1 : r t < 1 := H2_lt_one h1
  have hlim := tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
  have hpos : 0 < ε / (M + 1) := by positivity
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hlim (ε / (M + 1)) hpos
  refine ⟨N, fun n hn y hy => ?_⟩
  have hb := iter_bound hr0 hK n y hy
  have hsmall : r t ^ n < ε / (M + 1) := by
    have := hN n hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (pow_nonneg hr0 n)] at this
    exact this
  rw [Metric.mem_ball, Real.dist_eq, sub_zero]
  have : r t ^ n * M < ε := by
    have h2 : r t ^ n * (M + 1) < ε := by
      rw [lt_div_iff₀ (by linarith)] at hsmall; linarith
    nlinarith [pow_nonneg hr0 n]
  linarith

/-! ## The failure at the threshold -/

/-- At `t = 1` the first map is the identity, so every point survives every iterate. -/
theorem mem_iter_one (x : ℝ) : ∀ n : ℕ, x ∈ (step 1)^[n] ({x} : Set ℝ) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact Or.inl ⟨x, ih, by rw [r_one]; ring⟩

theorem not_attracts_one {x : ℝ} (hx : x ≠ 0) : ¬ AttractsFrom 1 ({x} : Set ℝ) := by
  intro h
  obtain ⟨N, hN⟩ := h |x| (abs_pos.mpr hx)
  have hmem := hN N le_rfl (mem_iter_one x N)
  rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hmem
  exact lt_irrefl _ hmem

/-- No open neighbourhood of `0` is a basin: each contains a nonzero point. -/
theorem no_basin (U : Set ℝ) (hU : IsOpen U) (h0 : (0 : ℝ) ∈ U) :
    ∃ x ∈ U, x ≠ 0 ∧ ¬ AttractsFrom 1 ({x} : Set ℝ) := by
  obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.mp hU 0 h0
  have hx : (0 : ℝ) < ε / 2 := by linarith
  refine ⟨ε / 2, hsub ?_, ne_of_gt hx, not_attracts_one (ne_of_gt hx)⟩
  rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hx]
  linarith

/-! ## The refutation -/

/-- The terminal-attraction conclusion of Conjecture 6.1 for this family. -/
def TerminalAttraction : Prop :=
  ∃ U : Set ℝ, IsOpen U ∧ (0 : ℝ) ∈ U ∧ ∀ x ∈ U, AttractsFrom 1 ({x} : Set ℝ)

theorem not_terminalAttraction : ¬ TerminalAttraction := by
  rintro ⟨U, hU, h0, hall⟩
  obtain ⟨x, hxU, _, hnot⟩ := no_basin U hU h0
  exact hnot (hall x hxU)

/-- Conjecture 6.1's conclusion, as the conjunction it is.  The uniqueness half is an
opaque `Prop`: it **holds** in this example, and nothing here refutes it. -/
def Conj61Conclusion (Uniqueness : Prop) : Prop := Uniqueness ∧ TerminalAttraction

/-- **Conjecture 6.1 is false**, whatever the uniqueness half says. -/
theorem not_conj61 (Uniqueness : Prop) : ¬ Conj61Conclusion Uniqueness :=
  fun h => not_terminalAttraction h.2

end Principia.MathDB.P354469
