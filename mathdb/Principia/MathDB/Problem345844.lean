import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

set_option autoImplicit false

/-!
# MathDB 345844 — the weighted harmonic Hardy constant is not continuous

Write-up: `mathdb-open-problems/problems/345844/solution.tex` on the `mathdb-results`
branch of `antoshashakov/Principia-Math-In-Progress`, "Discontinuity of the weighted
harmonic Hardy constant".  It **refutes Conjecture 1 of Pasteczka** (p. 1061): that a
symmetric, monotone weighted mean which is continuous in its weights and has the Hardy
property must have a Hardy constant continuous for pointwise convergence of positive
weight sequences.

## The witness

The weighted **harmonic** mean on `(0, ∞)`, with `W n = ∑_{i ≤ n} w i` and

  `hmean x w n = W n / ∑_{i ≤ n} (w i / x i)`,

and `H w` the least `C` with `∑ w n · hmean x w n ≤ C ∑ w n · x n`.  Take (indexing from
`0`, so the source's `4^{n-1}` is `4^n` here)

  `lam n = 4^n`,   `mu K n = 4^(min n K)`.

Then `mu K → lam` pointwise — they are **equal** at coordinate `n` as soon as `K ≥ n` —
while `H (mu K) ≥ 2` for every `K` and `H lam ≤ 4/3`.  The gap `2/3` never closes.

Both sequences are strictly positive **integers** with infinite total mass, so the
refutation survives restricting the conjecture to that smaller class
(`lam_pos`, `mu_pos`, `mu_eq_lam`).

## What is proved

* `W_lam`, `lam_ratio_lt` — `W lam n = (4^{n+1} - 1)/3`, and `W lam n / lam n < 4/3`.
* `hmean_le` — `hmean x w n ≤ (W w n / w n) · x n`, because the denominator sum is at
  least its own last term.  Combined with the previous line this gives the upper bound
  **termwise** (`lam_termwise`): no series manipulation is needed for `H lam ≤ 4/3`.
* `sum_w_mul_W` — the source's identity (4), `∑_{i ≤ n} w i · W i = (W n² + Q n)/2`.
* `tail_le` — the source's (3) at `i = 0`: `∑_{n ≤ L} w n / W n² ≤ 2 / w 0`, by
  `w (n+1)/W (n+1)² ≤ 1/W n - 1/W (n+1)` and telescoping.
* `gap_term`, `gap_nonneg`, `gap_le` — **the quantitative heart**:
  `0 ≤ 2·D L - T L ≤ 4B/w 0` whenever every `w i ≤ B`, where `D L = ∑ w n / W n` and
  `T L = ∑ 2 w n W n/(W n² + Q n)`.  The numerator is *bounded* while `D L` diverges,
  which is exactly what forces `T L / D L → 2`.
* `Setup.two_le_H` — hence `2 ≤ H (mu K)` for every `K`.
* `Setup.not_continuous` — the refutation.

## What is carried

Only the two analytic inputs the write-up itself supplies:

* `Setup.H_le` / `Setup.H_ge_ratio` — that `H` is the least admissible constant, and
  that testing the source's explicit input at level `L` gives `T L / D L ≤ H w` (the
  source's `H(w) ≥ T_L/(D_L+δ)`, then `δ ↓ 0`);
* `Setup.D_tendsto_atTop` — that `D L → ∞` for a bounded weight sequence of infinite
  total mass (the source's integral comparison `D_L ≥ log(1 + W_L/B)`).

Lemma 1 of the write-up (`H w ≤ 9/2` for every `w`, by Cauchy–Schwarz and Tonelli) is
what verifies the conjecture's *Hardy property* hypothesis; it is carried as
`Setup.hardy_property` and is not used in the refutation itself.

`Campaigns/MathDB-Formalization/verify_345844.py` checks every bound above in exact
rationals, and confirms the logarithmic rate: for `K = 1` the gap is exactly
`2(1 - 1/(L+1))`, so `2 - T_L/D_L = 2/D_L ~ 2/log L`.
-/

namespace Principia.MathDB.P345844

open Finset

/-! ## The weighted harmonic mean and its prefix data -/

/-- `W w n = ∑_{i ≤ n} w i`. -/
noncomputable def W (w : ℕ → ℝ) (n : ℕ) : ℝ := ∑ i ∈ range (n + 1), w i

/-- `Q w n = ∑_{i ≤ n} (w i)²`. -/
noncomputable def Q (w : ℕ → ℝ) (n : ℕ) : ℝ := ∑ i ∈ range (n + 1), w i ^ 2

/-- The weighted harmonic mean of the first `n+1` inputs. -/
noncomputable def hmean (x w : ℕ → ℝ) (n : ℕ) : ℝ :=
  W w n / ∑ i ∈ range (n + 1), w i / x i

/-- `D w L = ∑_{n ≤ L} w n / W n`. -/
noncomputable def D (w : ℕ → ℝ) (L : ℕ) : ℝ := ∑ n ∈ range (L + 1), w n / W w n

/-- `T w L = ∑_{n ≤ L} 2 w n W n / (W n² + Q n)`. -/
noncomputable def T (w : ℕ → ℝ) (L : ℕ) : ℝ :=
  ∑ n ∈ range (L + 1), 2 * w n * W w n / (W w n ^ 2 + Q w n)

theorem W_zero (w : ℕ → ℝ) : W w 0 = w 0 := by simp [W]

theorem W_succ (w : ℕ → ℝ) (n : ℕ) : W w (n + 1) = W w n + w (n + 1) := by
  simp [W, Finset.sum_range_succ]

theorem Q_succ (w : ℕ → ℝ) (n : ℕ) : Q w (n + 1) = Q w n + w (n + 1) ^ 2 := by
  simp [Q, Finset.sum_range_succ]

theorem W_pos {w : ℕ → ℝ} (hw : ∀ i, 0 < w i) (n : ℕ) : 0 < W w n :=
  Finset.sum_pos (fun i _ => hw i) ⟨0, by simp⟩

theorem Q_pos {w : ℕ → ℝ} (hw : ∀ i, 0 < w i) (n : ℕ) : 0 < Q w n :=
  Finset.sum_pos (fun i _ => pow_pos (hw i) 2) ⟨0, by simp⟩

theorem w_le_W {w : ℕ → ℝ} (hw : ∀ i, 0 < w i) (n : ℕ) : w n ≤ W w n := by
  rcases n with _ | m
  · simp [W_zero]
  · rw [W_succ]
    linarith [(W_pos hw m).le]

theorem W_mono {w : ℕ → ℝ} (hw : ∀ i, 0 < w i) (n : ℕ) : W w n ≤ W w (n + 1) := by
  rw [W_succ]; linarith [hw (n + 1)]

/-! ## The termwise upper bound -/

/-- `hmean x w n ≤ (W n / w n) · x n`: the denominator sum is at least its own last
term.  This is the only fact the upper half of the refutation needs, and it is
**termwise** — no series manipulation. -/
theorem hmean_le {x w : ℕ → ℝ} (hw : ∀ i, 0 < w i) (hx : ∀ i, 0 < x i) (n : ℕ) :
    hmean x w n ≤ W w n / w n * x n := by
  have hden : 0 < ∑ i ∈ range (n + 1), w i / x i :=
    Finset.sum_pos (fun i _ => div_pos (hw i) (hx i)) ⟨0, by simp⟩
  have hlast : w n / x n ≤ ∑ i ∈ range (n + 1), w i / x i := by
    refine Finset.single_le_sum (f := fun i => w i / x i) (fun i _ => ?_) (by simp)
    exact (div_pos (hw i) (hx i)).le
  have hpos : 0 < w n / x n := div_pos (hw n) (hx n)
  rw [hmean, div_le_iff₀ hden]
  have hfac : 0 < W w n / w n * x n := mul_pos (div_pos (W_pos hw n) (hw n)) (hx n)
  have hw0 : w n ≠ 0 := (hw n).ne'
  have hx0 : x n ≠ 0 := (hx n).ne'
  have key : W w n / w n * x n * (w n / x n) = W w n := by
    field_simp
  have h2 : W w n / w n * x n * (w n / x n)
      ≤ W w n / w n * x n * ∑ i ∈ range (n + 1), w i / x i :=
    mul_le_mul_of_nonneg_left hlast hfac.le
  linarith [key.le, key.ge]

/-! ## The sequence `lam n = 4ⁿ` -/

/-- The limiting weight sequence. -/
noncomputable def lam (n : ℕ) : ℝ := 4 ^ n

/-- The approximating weight sequences: `4ⁿ` until index `K`, constant afterwards. -/
noncomputable def mu (K n : ℕ) : ℝ := 4 ^ (min n K)

theorem lam_pos (n : ℕ) : 0 < lam n := by unfold lam; positivity

theorem mu_pos (K n : ℕ) : 0 < mu K n := by unfold mu; positivity

/-- `mu K → lam` pointwise, and not merely in the limit: the two sequences are **equal**
at coordinate `n` as soon as `K ≥ n`. -/
theorem mu_eq_lam {K n : ℕ} (h : n ≤ K) : mu K n = lam n := by
  unfold mu lam; rw [min_eq_left h]

/-- each `mu K` is bounded, by `4^K`. -/
theorem mu_le (K n : ℕ) : mu K n ≤ 4 ^ K := by
  unfold mu
  exact pow_le_pow_right₀ (by norm_num) (min_le_right n K)

theorem W_lam (n : ℕ) : W lam n = (4 ^ (n + 1) - 1) / 3 := by
  induction n with
  | zero => rw [W_zero, lam]; norm_num
  | succ m ih => rw [W_succ, ih]; unfold lam; ring

/-- `W lam n / lam n < 4/3`: the ratio rises to `4/3` but never reaches it. -/
theorem lam_ratio_lt (n : ℕ) : W lam n / lam n < 4 / 3 := by
  rw [W_lam, lam, div_lt_div_iff₀ (by positivity) (by norm_num)]
  have h : (0 : ℝ) < 4 ^ n := by positivity
  have h2 : (4 : ℝ) ^ (n + 1) = 4 * 4 ^ n := by ring
  rw [h2]; linarith

/-- **The upper bound, termwise.** -/
theorem lam_termwise {x : ℕ → ℝ} (hx : ∀ i, 0 < x i) (n : ℕ) :
    lam n * hmean x lam n ≤ 4 / 3 * (lam n * x n) := by
  have h1 := hmean_le lam_pos hx n
  have h2 := lam_ratio_lt n
  have h3 : hmean x lam n ≤ 4 / 3 * x n := by
    have := mul_le_mul_of_nonneg_right h2.le (hx n).le
    linarith
  nlinarith [lam_pos n, hx n]

/-! ## Identity (4) -/

/-- The write-up's identity (4): `∑_{i ≤ n} w i · W i = (W n² + Q n)/2`. -/
theorem sum_w_mul_W (w : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ range (n + 1), w i * W w i = (W w n ^ 2 + Q w n) / 2 := by
  induction n with
  | zero => simp [W, Q]; ring
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, W_succ, Q_succ]
    ring

/-! ## The telescoping tail bound (the source's (3) at `i = 0`) -/

theorem tail_step {w : ℕ → ℝ} (hw : ∀ i, 0 < w i) (n : ℕ) :
    w (n + 1) / W w (n + 1) ^ 2 ≤ 1 / W w n - 1 / W w (n + 1) := by
  have hn : 0 < W w n := W_pos hw n
  have hn1 : 0 < W w (n + 1) := W_pos hw (n + 1)
  have hmono : W w n ≤ W w (n + 1) := W_mono hw n
  have hw1 : 0 < w (n + 1) := hw (n + 1)
  have hsub : W w (n + 1) - W w n = w (n + 1) := by rw [W_succ]; ring
  have key : 1 / W w n - 1 / W w (n + 1) = w (n + 1) / (W w n * W w (n + 1)) := by
    rw [← hsub]
    field_simp
  rw [key]
  refine div_le_div_of_nonneg_left hw1.le (by positivity) ?_
  nlinarith [hn, hn1]

/-- **The source's (3) at `i = 0`**: `∑_{n ≤ L} w n / W n² ≤ 2 / w 0`. -/
theorem tail_le {w : ℕ → ℝ} (hw : ∀ i, 0 < w i) (L : ℕ) :
    ∑ n ∈ range (L + 1), w n / W w n ^ 2 ≤ 2 / w 0 := by
  have h0 : 0 < w 0 := hw 0
  have hsplit : ∑ n ∈ range (L + 1), w n / W w n ^ 2
      = (∑ n ∈ range L, w (n + 1) / W w (n + 1) ^ 2) + w 0 / W w 0 ^ 2 :=
    Finset.sum_range_succ' (fun n => w n / W w n ^ 2) L
  have htel : ∑ n ∈ range L, (1 / W w n - 1 / W w (n + 1)) = 1 / W w 0 - 1 / W w L :=
    Finset.sum_range_sub' (fun n => 1 / W w n) L
  have hstep : (∑ n ∈ range L, w (n + 1) / W w (n + 1) ^ 2)
      ≤ ∑ n ∈ range L, (1 / W w n - 1 / W w (n + 1)) :=
    Finset.sum_le_sum fun n _ => tail_step hw n
  rw [htel] at hstep
  have hWL : 0 < W w L := W_pos hw L
  have hfirst : w 0 / W w 0 ^ 2 = 1 / w 0 := by
    rw [W_zero]; field_simp
  rw [W_zero] at hstep
  rw [hsplit, hfirst]
  have hLpos : 1 / W w L > 0 := by positivity
  have h2 : (2 : ℝ) / w 0 = 1 / w 0 + 1 / w 0 := by ring
  linarith

/-! ## `Q n ≤ B · W n` -/

theorem Q_le_mul {w : ℕ → ℝ} (hw : ∀ i, 0 < w i) {B : ℝ} (hB : ∀ i, w i ≤ B) (n : ℕ) :
    Q w n ≤ B * W w n := by
  rw [Q, W, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have := hw i
  nlinarith [hB i]

/-! ## The uniform gap — the quantitative heart -/

/-- One term of `2·D - T`, in closed form. -/
theorem gap_term {w : ℕ → ℝ} (hw : ∀ i, 0 < w i) (n : ℕ) :
    2 * (w n / W w n) - 2 * w n * W w n / (W w n ^ 2 + Q w n)
      = 2 * w n * Q w n / (W w n * (W w n ^ 2 + Q w n)) := by
  have h1 : 0 < W w n := W_pos hw n
  have h2 : 0 < Q w n := Q_pos hw n
  have h3 : W w n ^ 2 + Q w n ≠ 0 := by positivity
  field_simp
  ring

theorem gap_eq {w : ℕ → ℝ} (hw : ∀ i, 0 < w i) (L : ℕ) :
    2 * D w L - T w L
      = ∑ n ∈ range (L + 1), 2 * w n * Q w n / (W w n * (W w n ^ 2 + Q w n)) := by
  rw [D, T, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun n _ => gap_term hw n

theorem gap_nonneg {w : ℕ → ℝ} (hw : ∀ i, 0 < w i) (L : ℕ) : 0 ≤ 2 * D w L - T w L := by
  rw [gap_eq hw]
  refine Finset.sum_nonneg fun n _ => ?_
  have h1 : 0 < W w n := W_pos hw n
  have h2 : 0 < Q w n := Q_pos hw n
  have h3 : 0 < w n := hw n
  positivity

/-- **`2·D L - T L ≤ 4B/w 0`, uniformly in `L`.**  `Q n ≤ B W n` shrinks each term to
`2B w n / W n²`, and the telescoping bound sums those. -/
theorem gap_le {w : ℕ → ℝ} (hw : ∀ i, 0 < w i) {B : ℝ} (hB : ∀ i, w i ≤ B) (L : ℕ) :
    2 * D w L - T w L ≤ 4 * B / w 0 := by
  have hB0 : 0 < B := lt_of_lt_of_le (hw 0) (hB 0)
  rw [gap_eq hw]
  have hterm : ∀ n ∈ range (L + 1),
      2 * w n * Q w n / (W w n * (W w n ^ 2 + Q w n)) ≤ 2 * B * (w n / W w n ^ 2) := by
    intro n _
    have h1 : 0 < W w n := W_pos hw n
    have h2 : 0 < Q w n := Q_pos hw n
    have h3 : 0 < w n := hw n
    have hQ := Q_le_mul hw hB n
    rw [div_le_iff₀ (by positivity)]
    have hexp : 2 * B * (w n / W w n ^ 2) * (W w n * (W w n ^ 2 + Q w n))
        = 2 * B * w n * (W w n ^ 2 + Q w n) / W w n := by
      field_simp
    rw [hexp, le_div_iff₀ h1]
    have hscale : 2 * w n * W w n * Q w n ≤ 2 * w n * W w n * (B * W w n) :=
      mul_le_mul_of_nonneg_left hQ (by positivity)
    nlinarith [hscale, mul_pos h3 h2, hB0]
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  have htail := tail_le hw L
  have : (2 : ℝ) * B * (∑ n ∈ range (L + 1), w n / W w n ^ 2) ≤ 2 * B * (2 / w 0) := by
    exact mul_le_mul_of_nonneg_left htail (by positivity)
  have heq : (2 : ℝ) * B * (2 / w 0) = 4 * B / w 0 := by
    field_simp
    norm_num
  linarith [this, heq.le, heq.ge]

/-! ## The carried analytic inputs, and the refutation -/

/-- The Hardy-constant function together with exactly the two analytic facts the
write-up supplies about it. -/
structure Setup where
  /-- the Hardy constant of a weight sequence -/
  H : (ℕ → ℝ) → ℝ
  /-- **CARRIED**: `H` is the LEAST admissible constant, so any termwise-verified
  bound on the weighted sums bounds it from above. -/
  H_le : ∀ (w : ℕ → ℝ) (C : ℝ), 0 ≤ C → (∀ i, 0 < w i) →
    (∀ (x : ℕ → ℝ), (∀ i, 0 < x i) → ∀ n, w n * hmean x w n ≤ C * (w n * x n)) →
    H w ≤ C
  /-- **CARRIED**: testing the write-up's explicit input at level `L` (and letting its
  parameter `δ ↓ 0`) gives `T L / D L ≤ H w`. -/
  H_ge_ratio : ∀ (w : ℕ → ℝ), (∀ i, 0 < w i) → ∀ L : ℕ, T w L / D w L ≤ H w
  /-- **CARRIED** (the write-up's integral comparison `D_L ≥ log(1 + W_L/B)`): for a
  bounded weight sequence of infinite total mass, `D L → ∞`. -/
  D_tendsto_atTop : ∀ (w : ℕ → ℝ), (∀ i, 0 < w i) → (∃ B, ∀ i, w i ≤ B) →
    (∀ M : ℝ, ∃ n, M ≤ W w n) →
    Filter.Tendsto (fun L => D w L) Filter.atTop Filter.atTop
  /-- **CARRIED** (the write-up's Lemma 1, by Cauchy–Schwarz and Tonelli): every
  positive weight sequence has a finite Hardy constant.  This is what verifies the
  conjecture's *Hardy property* hypothesis; the refutation does not use it. -/
  hardy_property : ∀ (w : ℕ → ℝ), (∀ i, 0 < w i) → H w ≤ 9 / 2

namespace Setup

variable (S : Setup)

/-- **`H lam ≤ 4/3`**, proved from the termwise bound alone. -/
theorem H_lam_le : S.H lam ≤ 4 / 3 :=
  S.H_le lam (4 / 3) (by norm_num) lam_pos fun x hx n => lam_termwise hx n

theorem D_pos {w : ℕ → ℝ} (hw : ∀ i, 0 < w i) (L : ℕ) : 0 < D w L :=
  Finset.sum_pos (fun n _ => div_pos (hw n) (W_pos hw n)) ⟨0, by simp⟩

/-- `T L / D L ≥ 2 - (4B/w 0)/D L`, the quantitative form of the lower bound. -/
theorem ratio_ge {w : ℕ → ℝ} (hw : ∀ i, 0 < w i) {B : ℝ} (hB : ∀ i, w i ≤ B) (L : ℕ) :
    2 - 4 * B / w 0 / D w L ≤ T w L / D w L := by
  have hD := D_pos hw L
  have hg := gap_le hw hB L
  have hnum : 0 ≤ T w L - 2 * D w L + 4 * B / w 0 := by linarith
  have hdiv : 0 ≤ (T w L - 2 * D w L + 4 * B / w 0) / D w L := div_nonneg hnum hD.le
  have key : T w L / D w L - (2 - 4 * B / w 0 / D w L)
      = (T w L - 2 * D w L + 4 * B / w 0) / D w L := by
    field_simp
    ring
  rw [← key] at hdiv
  linarith

/-- **`2 ≤ H w`** for a bounded positive weight sequence of infinite total mass. -/
theorem two_le_H {w : ℕ → ℝ} (hw : ∀ i, 0 < w i) {B : ℝ} (hB : ∀ i, w i ≤ B)
    (hmass : ∀ M : ℝ, ∃ n, M ≤ W w n) : 2 ≤ S.H w := by
  by_contra hcon
  rw [not_le] at hcon
  set ε := 2 - S.H w with hε
  have hεpos : 0 < ε := by simp [hε]; linarith
  have hB0 : 0 < B := lt_of_lt_of_le (hw 0) (hB 0)
  have hDinf := S.D_tendsto_atTop w hw ⟨B, hB⟩ hmass
  obtain ⟨L, hL⟩ := (Filter.tendsto_atTop.mp hDinf (4 * B / w 0 / ε + 1)).exists
  have hD := D_pos hw L
  have hw0 : 0 < w 0 := hw 0
  have hεne : ε ≠ 0 := hεpos.ne'
  have hquot : 4 * B / w 0 / D w L < ε := by
    rw [div_lt_iff₀ hD]
    have hstep : ε * (4 * B / w 0 / ε + 1) ≤ ε * D w L :=
      mul_le_mul_of_nonneg_left hL hεpos.le
    have hcancel : ε * (4 * B / w 0 / ε + 1) = 4 * B / w 0 + ε := by
      field_simp
    rw [hcancel] at hstep
    linarith
  have h1 := ratio_ge hw hB L
  have h2 := S.H_ge_ratio w hw L
  have : 2 - ε < T w L / D w L := by linarith
  rw [hε] at this
  simp only [sub_sub_cancel] at this
  linarith

/-- The `mu K` are bounded and have infinite total mass. -/
theorem mu_mass (K : ℕ) (M : ℝ) : ∃ n, M ≤ W (mu K) n := by
  have hstep : ∀ n, W (mu K) n + 1 ≤ W (mu K) (n + 1) := by
    intro n
    rw [W_succ]
    have h1 : (1 : ℝ) ≤ mu K (n + 1) := by
      unfold mu
      exact one_le_pow₀ (by norm_num)
    linarith
  have hgrow : ∀ n : ℕ, (n : ℝ) ≤ W (mu K) n := by
    intro n
    induction n with
    | zero => simp [W_zero]; exact (mu_pos K 0).le
    | succ m ih => push_cast; linarith [hstep m, ih]
  obtain ⟨n, hn⟩ := exists_nat_ge M
  exact ⟨n, le_trans hn (hgrow n)⟩

/-- **`2 ≤ H (mu K)` for every `K`.** -/
theorem two_le_H_mu (K : ℕ) : 2 ≤ S.H (mu K) :=
  S.two_le_H (mu_pos K) (mu_le K) (mu_mass K)

/-- **THE REFUTATION.**  `mu K` agrees with `lam` in every coordinate `n ≤ K`, so
`mu K → lam` pointwise; yet the Hardy constants stay `2/3` apart.  No function `H`
satisfying the carried properties can be continuous along this sequence. -/
theorem not_continuous :
    (∀ (n K : ℕ), n ≤ K → mu K n = lam n) ∧
      (∀ K : ℕ, 2 / 3 ≤ S.H (mu K) - S.H lam) := by
  refine ⟨fun n K h => mu_eq_lam h, fun K => ?_⟩
  have h1 := S.two_le_H_mu K
  have h2 := S.H_lam_le
  linarith

/-- and therefore no subsequence of the Hardy constants converges to `H lam`. -/
theorem not_tendsto : ¬ Filter.Tendsto (fun K => S.H (mu K)) Filter.atTop
    (nhds (S.H lam)) := by
  intro hcon
  have hgap := (S.not_continuous).2
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hcon (1 / 3) (by norm_num)
  have h := hgap N
  have hd := hN N le_rfl
  rw [Real.dist_eq, abs_lt] at hd
  linarith [hd.2]

end Setup

end Principia.MathDB.P345844
