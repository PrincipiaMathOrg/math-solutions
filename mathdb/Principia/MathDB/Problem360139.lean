import Mathlib
import Principia.Common.SpacingSum
import Principia.Common.TanhMajorant

set_option autoImplicit false

/-!
# MathDB #360139 — positivity of the Fibonacci characteristic function

Write-up `mathdb-open-problems/problems/360139/solution.tex` on the `mathdb-results` branch
of `antoshashakov/Principia-Math-In-Progress`.
Source: A. Pouti, C. Ramsey and N. Strungaru, *Generating functions of substitutions*,
arXiv:2309.16100v2, **Conjecture 5.12**.

For the Fibonacci substitution `σ(a) = ab`, `σ(b) = a` with fixed word `w = abaababa…`, the
indicator generating function is `C_a(z) = ∑_{j≥0} 1[w_j = a]·z^j`, and Conjecture 5.12
asserts `C_a(x) > 0` for every real `x ∈ (-1,1)`.

## The shape of the argument, and what this module supplies

`x ∈ [0,1)` is immediate (nonnegative coefficients, constant term `1`).  For `x = -t` the
write-up produces an exact ALTERNATING series

    C_a(-t) = 1/(1+t) + ∑_{k≥0} (-1)^k E_k(t),     E_k > 0,

and bounds the negative terms by an AM–GM majorant: `E_k ≤ ((1+t)/t²)·g(t^{c_k})` with

    g(u) = u(1-u)/(1+u)².

The negative terms sit at `c_{2ℓ+1} = F_{6ℓ+7}`, and `F_{m+6} > 16 F_m`, so with
`x_ℓ = -F_{6ℓ+7}·log t` the spacing satisfies `x_{ℓ+1} ≥ 16 x_ℓ`.  The **spacing lemma** is
that any such sequence has `∑_ℓ g(e^{-x_ℓ}) < 127/600`, and it is proved by a three-way
split whose three bounds sum to `127/600` EXACTLY:

    x < 1/4    : g(e^{-x}) ≤ x/4,   backward geometric sum  →  1/15
    1/4 ≤ x < 4: at most one term,  g ≤ 1/8                 →  1/8
    x ≥ 4      : g(e^{-x}) ≤ e^{-x}                         →  1/50

and `1/15 + 1/8 + 1/50 = 127/600`.

**This module proves the four analytic ingredients of that split** and carries the
combinatorial and series links as named hypotheses.

## `Real.tanh y ≤ y` is a genuine Mathlib gap, and it is NOT optional

`tanh_le_self` is proved here.  Mathlib has `Real.tanh_eq_sinh_div_cosh`, `Real.self_lt_sinh`
and the `artanh` development, but **no** `tanh y ≤ y` — grepped, zero hits.  It is exactly
what makes the first bound `g(e^{-x}) ≤ x/4` rather than `x/2`: writing `u = e^{-x}`,

    g(u) = [u/(1+u)]·[(1-u)/(1+u)] = [1/(e^x+1)]·tanh(x/2) ≤ (1/2)·(x/2) = x/4.

The naive weakening `(1-u)/(1+u) ≤ x` inflates the first bound from `1/15` to `2/15`, which
makes the write-up's final constant `1 - (127/600 + 1/15)(19/9)²` NEGATIVE and destroys the
proof.  So the gap is load-bearing, not cosmetic.

The other two bounds have exact certificates rather than estimates:

* `gfun_le_eighth` — `1/8 - g(u) = (3u-1)²/(8(1+u)²)`, an exact square, so the bound is
  attained at `u = 1/3` and is sharp.
* `gfun_le_self` — `u - g(u) = u²(u+3)/(1+u)²`.

## What is NOT proved here

`SeriesMajorant` alone — and **what remains inside it is much smaller than this section used
to claim**.  It said "the telescoping identity producing the alternating series, the AM–GM
majorant, and the assembly", and the first of those was priced as Fibonacci-WORD
combinatorics.  Both the telescoping identity and the majorant are now PROVED (see §"The
telescoping expansion — and it needs NO word combinatorics"): they follow from the
recurrence `P_{n+1} = P_n + z^{L_n} P_{n-1}` alone, and **so is the assembly** (see
§"The assembly, and the carried link restated").

**NOTHING IS CARRIED.**  `PrefixLimit` — the convergence of the periodic-prefix
approximants, the one place the Fibonacci word was needed — is PROVED, as
`prefixLimit_CaFib` (see §"The Fibonacci word, and `PrefixLimit` DISCHARGED").  `C_a` is a
DEFINED object here, `CaFib`, the generating function of the `a`-positions of the fixed
word, tied to the source by three anchors: the concatenation recurrence, `subst_fibWord`
(`A_{n+1} = σ(A_n)`, so `A_n = σ^n(a)`) and `fibWord_five` (the printed prefix
`w = abaababa…`).

**THE THEOREM IS COMPLETE.**  `conjecture_5_12` proves the source's Conjecture 5.12 on its
whole interval:

    C_a(x) > 0   for every   x ∈ (-1,1).

Three regimes meet, and **two of the three thresholds are where the BOUNDS stop, not numbers
anyone chose**:

* `positive_of_six_sevenths` — `t ≥ 6/7`.  The telescoping bound is positive exactly when
  `473t² - 254t - 127 > 0`, i.e. `t > 0.85210…`; `9/10` was the write-up's rounding.
* `positive_of_small` — `t < 1/2`.  Discard every even term: `C_a(-t) ≥ 1 - t/(1-t)`, which
  is positive exactly for `t < 1/2` and EXACTLY zero there.
* `positive_on_band` — `1/2 ≤ t ≤ 6/7`, by truncation at `N = 12` with the even terms KEPT,
  leaving the degree-12 positivity `1 - t³ - t⁴ + t⁸ + t⁹ - t¹¹ - t¹² > 0`.
* `positive_of_nonneg` — `x ∈ [0,1)`, where in fact `C_a(x) ≥ 1` (`one_le_CaFib`), which is
  the write-up's own remark.

**Nothing is carried**, and `C_a` is `CaFib`, DEFINED here and tied to the source by three
anchors: the concatenation recurrence, `subst_fibWord` (`A_{n+1} = σ(A_n)`, hence
`A_n = σⁿ(a)`) and `fibWord_five` (the printed word `w = abaababa…`).  The write-up's Tasks
2–5 are explicitly *"questions for further work, not additional solved claims"*.

`SeriesMajorant` is kept but is no longer what the spine runs on.  Narrowing it to `∃ n` over
PARTIAL sums overshot: subtracting a partial sum instead of the whole one makes the left side
LARGER, so that form is strictly stronger than the consumers need and stronger than this
route delivers.  **A narrowing can land on a statement harder than the one it replaced; the
test is whether the CONSUMERS got smaller, not whether the wording got tighter.**

**The lesson is about the description, not the mathematics.**  A carried obligation's prose
is written when the spine is young, and prices its sub-steps by the machinery the SOURCE
used rather than by what the step needs.  Re-deriving it from the write-up cost one reading
and removed the largest apparent obstacle in the row.

*No longer carried*: `SpacingLemma` (see §"The spacing lemma, discharged") and the
Fibonacci growth (see §"The Fibonacci growth, and the narrowing of `SeriesMajorant`").
The carried Prop was also NARROWED on 2026-09-24: its old form asserted `∃ x, Spaced x ∧ P`
where `P` does not mention `x`, so the spacing was inert and `127/600` was assumed rather
than used.  It now assumes the majorant at the write-up's own exponents and at the actual
partial sum, with `127/600` supplied by `spacingLemma`; `seriesMajorantOld_of` proves the
new form implies the old.

**A scope difference worth stating.**  The source's Lemma is `∑_{ℓ≥0} g(e^{−x_ℓ}) < 127/600`
— STRICT, and over the INFINITE sum.  The `SpacingLemma` proved here is `≤ 127/600` for
every PARTIAL sum, which is weaker on both counts.  It is what the spine consumes, but it is
not the source's lemma, and nothing here should be read as claiming otherwise.

**A recorded shortcut, for whoever finishes the row.**  The write-up handles the remaining
interval `t ∈ [0,9/10]` by a separate `w = σ³(w)` fixed-point block decomposition — the only
part of the argument needing real word-combinatorics infrastructure.  A subagent audit found
that section is replaceable by a single truncated-series inequality with margin `≥ 0.42`,
reusing machinery already needed for `t` near `1`.  That is the largest available
cost reduction and it is invisible from the write-up.

**A recorded trap.**  `MeasureTheory.charFun` is the probabilistic Fourier–Stieltjes
transform of a measure and is NOT this object; a Lean statement must not drift into it.
Likewise `2 ∣ fib n ↔ 3 ∣ n` looks like a Mathlib gap and is not — `Nat.fib_gcd 3 n` gives
it in a few lines.  **Now proved**, as `two_dvd_fib_iff`, and it earns its place: it is what
turns `1 - (-t)^m` into `1 + t^m`, so every sign in the specialisation `z = -t` rests on it.
-/

namespace Principia.MathDB.P360139

open Real Principia.Common

/-! ### The analytic majorant, PROMOTED

`tanh y ≤ y`, its supporting `sinh y ≤ y·cosh y`, and the majorant `g(u) = u(1-u)/(1+u)²` with its
four bounds mention no substitution, no Fibonacci word and no generating function, so they now live
in `Principia.Common.TanhMajorant` -- where the next campaign can find them, and where the record
that Mathlib lacks `tanh_le_self` is visible outside this row.  The names are unchanged; this
module opens `Principia.Common`, so every use below reads exactly as before.
-/

/-! ### The spacing apparatus, PROMOTED

`Spaced`, `SpacingLemma` and its proof `spacingLemma`, together with the geometric, exponential
and growth lemmas they run on, quantify over an ARBITRARY `x : N -> R` and mention no Fibonacci
object at all.  They now live in `Principia.Common.SpacingSum`.  What stays here is the
INSTANTIATION -- that Fibonacci growth supplies such an `x` -- which is the only campaign-specific
part of the argument.  The names are unchanged, and this module already opens `Principia.Common`.
-/

/-! ### The spine

The analytic ingredients above are proved.  What remains are the word-combinatorial and
series links, carried as named hypotheses: the telescoping identity that produces the
alternating series, and the AM–GM majorant.  (The Fibonacci growth that gives the spacing
was carried too until 2026-09-24; it is now proved — see the last section.) -/

/-! ### The Fibonacci growth, and the narrowing of `SeriesMajorant`

`SeriesMajorant` was stated as

    ∀ t ∈ [9/10, 1), ∃ x, Spaced x ∧ 1/(1+t) - (1+t)/t²·(127/600) ≤ Ca(-t)

and **that existential is inert**: the conclusion never mentions `x`, so the statement is
equivalent to `(∃ x, Spaced x) ∧ …`, and `x_ℓ = 16^ℓ` satisfies the first conjunct
(`spaced_pow_sixteen`) while having nothing to do with the problem.  The spacing was
decoration, and the constant `127/600` was ASSUMED even though `spacingLemma` above now
proves it.

The version below instead assumes the representation-and-majorant step at the write-up's OWN
exponents `x_ℓ = -F_{6ℓ+7} log t` and at the ACTUAL partial sum, with `127/600` supplied
locally.  It is strictly weaker — `seriesMajorantOld_of` derives the old form from it — and
it makes the spacing load-bearing: `fib_partial_sum_le` is unavailable without
`spaced_fibWitness`.

**A defect in the write-up, found by formalising it.**  The spacing is justified by
`F_{m+6} = 13 F_m + 8 F_{m-1} > 17 F_m`, which needs `8 F_{m-1} > 4 F_m`.  At `m = 1` that
reads `8·F_0 = 0 > 4`, and the conclusion fails outright: `F_7 = 13 < 16 = 16·F_1`
(`fib_one_counterexample`, by `decide`).  The claim as USED is safe, because the witness
index is `6ℓ+7 ≥ 7` — but the stated reason is not a theorem, and formalising it verbatim
would fail.  The repair is a SHIFT rather than a side condition: stated from `n+2` there is
no boundary case at all, and `n = 0` is then the tight case `16·F_2 = 16 ≤ 21 = F_8`.
Checked first in `Campaigns/MathDB-Formalization/verify_360139_fib.py`, whose check (2)
asserts the violation set is EXACTLY `{1}`. -/

/-- `F_{n+8} = 13 F_{n+2} + 8 F_{n+1}`, the write-up's identity shifted so that no index is
`n - 1` — which is where its deduction breaks. -/
theorem fib_step (n : ℕ) :
    Nat.fib (n + 8) = 13 * Nat.fib (n + 2) + 8 * Nat.fib (n + 1) := by
  simp only [Nat.fib_add_two]
  ring

/-- **The boundary case the write-up's own deduction misses.** -/
theorem fib_one_counterexample : ¬ (16 * Nat.fib 1 ≤ Nat.fib 7) := by decide

/-- **`16 F_{n+2} ≤ F_{n+8}`.**  Only `F_{n+2} ≤ 2 F_{n+1}` is needed, giving
`8 F_{n+1} ≥ 3 F_{n+2}` and hence the coefficient `13 + 3 = 16`. -/
theorem fib_sixteen (n : ℕ) : 16 * Nat.fib (n + 2) ≤ Nat.fib (n + 8) := by
  have h := fib_step n
  have h2 : Nat.fib (n + 2) ≤ 2 * Nat.fib (n + 1) := by
    rw [Nat.fib_add_two]
    have := Nat.fib_le_fib_succ (n := n)
    omega
  omega

/-- The write-up's exponent sequence `x_ℓ = -F_{6ℓ+7} · log t`. -/
noncomputable def fibWitness (t : ℝ) : ℕ → ℝ :=
  fun ℓ => -(Nat.fib (6 * ℓ + 7) : ℝ) * Real.log t

theorem fib_witness_pos (ℓ : ℕ) : 0 < Nat.fib (6 * ℓ + 7) :=
  Nat.fib_pos.mpr (by omega)

/-- **The write-up's witness is spaced.**  Positivity is `F_{6ℓ+7} > 0` together with
`log t < 0`; the growth is `fib_sixteen` at `n = 6ℓ + 5`. -/
theorem spaced_fibWitness {t : ℝ} (h0 : 0 < t) (h1 : t < 1) : Spaced (fibWitness t) := by
  have hlog : Real.log t < 0 := Real.log_neg h0 h1
  constructor
  · intro ℓ
    have hf : (0 : ℝ) < (Nat.fib (6 * ℓ + 7) : ℝ) := by
      exact_mod_cast fib_witness_pos ℓ
    simp only [fibWitness]
    nlinarith
  · intro ℓ
    have hle : (16 : ℝ) * (Nat.fib (6 * ℓ + 7) : ℝ) ≤ (Nat.fib (6 * (ℓ + 1) + 7) : ℝ) := by
      have h := fib_sixteen (6 * ℓ + 5)
      have e1 : 6 * ℓ + 5 + 2 = 6 * ℓ + 7 := by ring
      have e2 : 6 * ℓ + 5 + 8 = 6 * (ℓ + 1) + 7 := by ring
      rw [e1, e2] at h
      exact_mod_cast h
    simp only [fibWitness]
    nlinarith

/-- The partial sums at the write-up's own witness are below `127/600`.  This is where
`spacingLemma` and `spaced_fibWitness` meet. -/
theorem fib_partial_sum_le {t : ℝ} (h0 : 0 < t) (h1 : t < 1) (n : ℕ) :
    ∑ ℓ ∈ Finset.range n, gfun (exp (-(fibWitness t ℓ))) ≤ 127 / 600 :=
  spacingLemma _ (spaced_fibWitness h0 h1) n

/-- **The narrowed carried link.**  The representation and AM-GM majorant, at the
write-up's own exponents and at the actual partial sum. -/
def SeriesMajorant (Ca : ℝ → ℝ) : Prop :=
  ∀ t : ℝ, 9 / 10 ≤ t → t < 1 →
    ∃ n : ℕ,
      1 / (1 + t) - (1 + t) / t ^ 2 *
          (∑ ℓ ∈ Finset.range n, gfun (exp (-(fibWitness t ℓ)))) ≤ Ca (-t)

-- SPEC-CARRY-CHECKED: SeriesMajorant -- 2026-09-26, against the capstone's signature.
-- `conjecture_5_12 (x : ℝ) (h : x ∈ Set.Ioo (-1) 1) : 0 < CaFib x` carries NO hypothesis, and
-- `CaFib` is defined in this file, so the counted claim does not run through this Prop.  It is a
-- deliberate vestigial carry, kept so the 2026-09-24 narrowing stays checkable, and it is now
-- provably inhabited (`exists_seriesMajorant`).

/-! #### `SeriesMajorant` is inhabited

`check_unsatisfied_specs.py` flags this Prop as consumed with no producer, and flags it as the
**highest-risk** such cell because this row is counted as fully verified.  Checked against the
capstone's signature, which is the thing that cannot go stale: `conjecture_5_12` reads
`(x : ℝ) (h : x ∈ Set.Ioo (-1) 1) : 0 < CaFib x` — **no carried hypothesis at all**, and `CaFib`
is defined in this file.  So the counted claim does not run through `SeriesMajorant`; the Prop
survives only as the two non-spine consumers below, kept deliberately so the 2026-09-24 narrowing
stays checkable.

Satisfiability is settled here anyway, so the flag has an answer rather than a judgement.  **It is
a weak statement and is labelled as such**: the witness is a constant function, *not* the source's
`C_a`, so it establishes only that `seriesMajorantOld_of` and `positive_near_one` are not vacuous.
It does not strengthen anything about `CaFib`, which needs no hypothesis. -/

/-- **`SeriesMajorant` is inhabited** — take `n = 0`, where the subtracted partial sum is empty and
the left side is `1/(1+t) ≤ 1/(19/10) < 1`. -/
theorem seriesMajorant_const_one : SeriesMajorant (fun _ => 1) := by
  intro t ht _
  refine ⟨0, ?_⟩
  have hpos : (0 : ℝ) < 1 + t := by linarith
  simp only [Finset.range_zero, Finset.sum_empty, mul_zero, sub_zero]
  rw [div_le_one hpos]
  linarith

/-- So the two consumers below are implications from a satisfiable hypothesis. -/
theorem exists_seriesMajorant : ∃ Ca : ℝ → ℝ, SeriesMajorant Ca :=
  ⟨fun _ => 1, seriesMajorant_const_one⟩

/-- The form this module carried until 2026-09-24, kept so the weakening is checkable. -/
def SeriesMajorantOld (Ca : ℝ → ℝ) : Prop :=
  ∀ t : ℝ, 9 / 10 ≤ t → t < 1 →
    ∃ x : ℕ → ℝ, Spaced x ∧
      1 / (1 + t) - (1 + t) / t ^ 2 * (127 / 600) ≤ Ca (-t)

/-- **The old statement's existential was inert.**  `16^ℓ` is spaced, so the conjunct that
looked like it recorded the spacing is satisfied by an unrelated sequence. -/
theorem spaced_pow_sixteen : Spaced (fun ℓ => (16 : ℝ) ^ ℓ) := by
  refine ⟨fun ℓ => by positivity, fun ℓ => ?_⟩
  simp [pow_succ]
  ring_nf
  nlinarith [pow_pos (by norm_num : (0:ℝ) < 16) ℓ]

/-- **The narrowed form implies the old one**, so the weakening loses nothing: the partial
sum is at most `127/600` and the coefficient `(1+t)/t²` is positive. -/
theorem seriesMajorantOld_of (Ca : ℝ → ℝ) (h : SeriesMajorant Ca) :
    SeriesMajorantOld Ca := by
  intro t h9 h1
  have ht0 : (0 : ℝ) < t := by linarith
  have h1t : (0 : ℝ) < 1 + t := by linarith
  have ht2 : (0 : ℝ) < t ^ 2 := by positivity
  obtain ⟨n, hn⟩ := h t h9 h1
  refine ⟨fun ℓ => (16 : ℝ) ^ ℓ, spaced_pow_sixteen, ?_⟩
  have hsum := fib_partial_sum_le ht0 h1 n
  have hc : (0 : ℝ) < (1 + t) / t ^ 2 := by positivity
  nlinarith

/-- **The negative half, now from the narrowed link.**  For `9/10 ≤ t < 1`,
`C_a(-t) ≥ 2753/(48600(1+t)) > 2753/97200 > 0`. -/
theorem positive_near_one (Ca : ℝ → ℝ) (hrep : SeriesMajorant Ca)
    (t : ℝ) (h9 : 9 / 10 ≤ t) (h1 : t < 1) : 0 < Ca (-t) := by
  obtain ⟨n, hn⟩ := hrep t h9 h1
  have ht0 : (0 : ℝ) < t := by linarith
  have h1t : (0 : ℝ) < 1 + t := by linarith
  have ht2 : (0 : ℝ) < t ^ 2 := by positivity
  have hsum := fib_partial_sum_le ht0 h1 n
  have hc : (0 : ℝ) < (1 + t) / t ^ 2 := by positivity
  have hkey : 0 < 1 / (1 + t) - (1 + t) / t ^ 2 * (127 / 600) := by
    have e : 1 / (1 + t) - (1 + t) / t ^ 2 * (127 / 600)
        = (600 * t ^ 2 - 127 * (1 + t) ^ 2) / (600 * t ^ 2 * (1 + t)) := by
      field_simp
    rw [e]
    apply div_pos _ (by positivity)
    nlinarith [sq_nonneg (t - 1), sq_nonneg (t - 9 / 10)]
  nlinarith

/-! ### The telescoping expansion — and it needs NO word combinatorics

The module's own summary of what is left said the carried `SeriesMajorant` includes "the
telescoping identity producing the alternating series", which reads as a job about
substitution words.  **It is not.**  Reading the write-up's derivation, every step from the
definition of `P_n` to the exact increment `(-1)^k E_k(t)` uses only the RECURRENCE

    P_{-1} = 0,  P_0 = 1,  P_{n+1} = P_n + z^{L_n} P_{n-1},    L_n = F_{n+2},

and the Fibonacci word is needed at exactly ONE place — that `f_n(z) = P_n(z)/(1 - z^{L_n})`
converges to `C_a(z)`.  This section proves the whole algebraic half.

* `prefixP` is the recurrence, indexed so `prefixP z (n+1)` is the write-up's `P_n`.
* `Dseq_succ` and `Dseq_eq` are `D_{n+1} = -z^{L_n} D_n` and its closed form; the only
  arithmetic anywhere in them is `F_{n+1} + F_{n+2} = F_{n+3}`.
* `prefixP_add_four` is the write-up's triple expansion.  **The write-up derives it from the
  word identity `A_{n+3} = A_n A_{n-1} A_n A_n A_{n-1}`; three uses of the recurrence give
  it, and after `pow_add` it is `ring`.**
* `triple_identity`/`triple_closed` are equation (eq:triple).
* `two_dvd_fib_iff` is the parity fact the module header flagged as a NON-gap, now proved:
  `F_m` is even exactly when `3 ∣ m`, from `Nat.fib_gcd` and `fib 3 = 2`.  It is what turns
  `1 - (-t)^m` into `1 + t^m`, and it is the only place parity is used.
* `increment_eq` is the exact increment `f_{3k+3}(-t) - f_{3k}(-t) = (-1)^k E_k(t)`.
* `amgm_denom` and `Efun_le_majorant` are (eq:majorant).  The write-up cites AM–GM; the
  exact certificate is shorter and needs no inequality lemma — with `s = F_{3k+3}` one has
  `a = c - s`, `d = c + s`, and `t^a + t^d - 2t^c = t^a(t^s - 1)^2`.
* `Efun_nonneg` is what licenses the assembly's step of DISCARDING the positive increments.

**What these are NOT yet wired into.**  `SeriesMajorant` is still carried as stated.  The
consumer that will discharge it needs one further input — that `f_n(-t) → C_a(-t)` — plus
the alternating-series assembly against `spacingLemma`, which is already proved.  The
numerics are in `Campaigns/MathDB-Formalization/verify_360139_telescope.py`, whose FIRST
check is the positive control that matters here: the recurrence really does reproduce the
word's prefix count, for `n = 0..16`. -/

/-- The prefix polynomials, indexed so that `prefixP z (n + 1)` is the write-up's `P_n` and
`prefixP z 0` is its `P_{-1} = 0`.  **This is a RECURRENCE, not a word count**: the
write-up's `P_{n+1} = P_n + z^{L_n} P_{n-1}` determines the whole family, and everything the
telescoping argument does with it is algebra. -/
noncomputable def prefixP (z : ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => 1
  | (n + 2) => prefixP z (n + 1) + z ^ Nat.fib (n + 2) * prefixP z n

theorem prefixP_zero (z : ℝ) : prefixP z 0 = 0 := rfl

theorem prefixP_one (z : ℝ) : prefixP z 1 = 1 := rfl

theorem prefixP_succ_succ (z : ℝ) (n : ℕ) :
    prefixP z (n + 2) = prefixP z (n + 1) + z ^ Nat.fib (n + 2) * prefixP z n := rfl

/-- The write-up's `D_n = P_n(1 - z^{L_{n-1}}) - P_{n-1}(1 - z^{L_n})`. -/
noncomputable def Dseq (z : ℝ) (n : ℕ) : ℝ :=
  prefixP z (n + 1) * (1 - z ^ Nat.fib (n + 1)) - prefixP z n * (1 - z ^ Nat.fib (n + 2))

theorem Dseq_zero (z : ℝ) : Dseq z 0 = 1 - z := by
  simp [Dseq, prefixP_zero, prefixP_one]

/-- `D_{n+1} = -z^{L_n} D_n`.  The whole content is `F_{n+1} + F_{n+2} = F_{n+3}`. -/
theorem Dseq_succ (z : ℝ) (n : ℕ) :
    Dseq z (n + 1) = -(z ^ Nat.fib (n + 2)) * Dseq z n := by
  have hfib : Nat.fib (n + 3) = Nat.fib (n + 1) + Nat.fib (n + 2) := Nat.fib_add_two
  simp only [Dseq, prefixP_succ_succ, hfib, pow_add]
  ring

theorem two_le_fib (n : ℕ) : 2 ≤ Nat.fib (n + 3) := by
  have hm : Nat.fib 3 ≤ Nat.fib (n + 3) := Nat.fib_mono (by omega)
  have h3 : Nat.fib 3 = 2 := by decide
  omega

/-- **The closed form**, `D_n = (-1)^n z^{L_{n+1} - 2}(1 - z)`.  The natural-number
subtraction never truncates, because `F_{n+3} ≥ 2`. -/
theorem Dseq_eq (z : ℝ) (n : ℕ) :
    Dseq z n = (-1) ^ n * z ^ (Nat.fib (n + 3) - 2) * (1 - z) := by
  induction n with
  | zero =>
    have h3 : Nat.fib 3 = 2 := by decide
    rw [Dseq_zero, h3]
    norm_num
  | succ n ih =>
    have hfib : Nat.fib (n + 4) = Nat.fib (n + 2) + Nat.fib (n + 3) := Nat.fib_add_two
    have hsub : Nat.fib (n + 4) - 2 = Nat.fib (n + 2) + (Nat.fib (n + 3) - 2) := by
      have := two_le_fib n
      omega
    rw [Dseq_succ, ih, hsub, pow_add]
    ring

/-- **The write-up's triple expansion**, `P_{n+3} = P_n(1 + z^{L_{n+1}} + z^{L_{n+2}}) +
P_{n-1}(z^{L_n} + z^{L_{n+2}+L_n})`.

The write-up derives it from the WORD identity `A_{n+3} = A_n A_{n-1} A_n A_n A_{n-1}`.  It
does not need one: three applications of the recurrence give it, and after `pow_add` the
whole thing is `ring`. -/
theorem prefixP_add_four (z : ℝ) (n : ℕ) :
    prefixP z (n + 4)
      = prefixP z (n + 1) * (1 + z ^ Nat.fib (n + 3) + z ^ Nat.fib (n + 4))
        + prefixP z n
            * (z ^ Nat.fib (n + 2) + z ^ (Nat.fib (n + 4) + Nat.fib (n + 2))) := by
  rw [prefixP_succ_succ z (n + 2), prefixP_succ_succ z (n + 1), prefixP_succ_succ z n,
    pow_add]
  ring

/-- **Equation (eq:triple)**: `P_{n+3}(1 - z^a) - P_n(1 - z^d) = -z^a(1 + z^c)·D_n`, with
`a = L_n = F_{n+2}`, `c = L_{n+2} = F_{n+4}` and `d = L_{n+3} = F_{n+5}`. -/
theorem triple_identity (z : ℝ) (n : ℕ) :
    prefixP z (n + 4) * (1 - z ^ Nat.fib (n + 2))
        - prefixP z (n + 1) * (1 - z ^ Nat.fib (n + 5))
      = -(z ^ Nat.fib (n + 2)) * (1 + z ^ Nat.fib (n + 4)) * Dseq z n := by
  have h3 : Nat.fib (n + 3) = Nat.fib (n + 1) + Nat.fib (n + 2) := Nat.fib_add_two
  have h4 : Nat.fib (n + 4) = Nat.fib (n + 2) + (Nat.fib (n + 1) + Nat.fib (n + 2)) := by
    rw [show n + 4 = (n + 2) + 2 from rfl, Nat.fib_add_two, h3]
  have h5 : Nat.fib (n + 5)
      = (Nat.fib (n + 1) + Nat.fib (n + 2))
          + (Nat.fib (n + 2) + (Nat.fib (n + 1) + Nat.fib (n + 2))) := by
    rw [show n + 5 = (n + 3) + 2 from rfl, Nat.fib_add_two, h3, h4]
  rw [prefixP_add_four, Dseq, h5, h4, h3]
  simp only [pow_add]
  ring

/-- **(eq:triple) in closed form**, the write-up's `(-1)^{n+1} z^{c-2}(1 + z^c)(1 - z)`. -/
theorem triple_closed (z : ℝ) (n : ℕ) :
    prefixP z (n + 4) * (1 - z ^ Nat.fib (n + 2))
        - prefixP z (n + 1) * (1 - z ^ Nat.fib (n + 5))
      = (-1) ^ (n + 1) * z ^ (Nat.fib (n + 4) - 2) * (1 + z ^ Nat.fib (n + 4)) * (1 - z) := by
  have hfib : Nat.fib (n + 4) = Nat.fib (n + 2) + Nat.fib (n + 3) := Nat.fib_add_two
  have hsub : Nat.fib (n + 4) - 2 = Nat.fib (n + 2) + (Nat.fib (n + 3) - 2) := by
    have := two_le_fib n
    omega
  rw [triple_identity, Dseq_eq, hsub, pow_add]
  ring

/-- **`F_m` is even exactly when `3 ∣ m`.**  The module header records this as something that
LOOKS like a Mathlib gap and is not: `Nat.fib_gcd` makes `fib` a strong divisibility
sequence, and `fib 3 = 2`, so `2 ∣ F_m ↔ fib (gcd 3 m) = 2 ↔ gcd 3 m = 3 ↔ 3 ∣ m`.  The
middle step needs only that `gcd 3 m` divides the prime `3`, and that `fib 1 = 1`. -/
theorem two_dvd_fib_iff (m : ℕ) : 2 ∣ Nat.fib m ↔ 3 ∣ m := by
  have h3 : Nat.fib 3 = 2 := by decide
  constructor
  · intro h
    have hdvd : Nat.fib 3 ∣ Nat.fib m := by rw [h3]; exact h
    have hgcd : Nat.fib (Nat.gcd 3 m) = Nat.fib 3 := by
      rw [Nat.fib_gcd]
      exact Nat.gcd_eq_left_iff_dvd.mpr hdvd
    have hcases : Nat.gcd 3 m = 1 ∨ Nat.gcd 3 m = 3 :=
      (Nat.prime_three).eq_one_or_self_of_dvd _ (Nat.gcd_dvd_left 3 m)
    rcases hcases with h1 | h1
    · rw [h1, h3] at hgcd
      exact absurd hgcd (by decide)
    · exact Nat.gcd_eq_left_iff_dvd.mp h1
  · intro h
    have hdvd : Nat.fib 3 ∣ Nat.fib m := Nat.fib_dvd 3 m h
    rw [h3] at hdvd
    exact hdvd

/-- The Fibonacci indices the increment `E_k` uses are all ODD, which is what turns
`1 - (-t)^m` into `1 + t^m` and fixes every sign in the specialisation `z = -t`. -/
theorem fib_odd_of_not_dvd {m : ℕ} (h : ¬ (3 ∣ m)) : Odd (Nat.fib m) := by
  rcases Nat.even_or_odd (Nat.fib m) with he | ho
  · exact absurd ((two_dvd_fib_iff m).mp he.two_dvd) h
  · exact ho

/-! ### The specialisation `z = -t`, and the write-up's `E_k` -/

/-- The write-up's `f_n(z) = P_n(z)/(1 - z^{L_n})`. -/
noncomputable def fapprox (z : ℝ) (n : ℕ) : ℝ :=
  prefixP z (n + 1) / (1 - z ^ Nat.fib (n + 2))

/-- The write-up's increment `E_k(t)`.  Its denominator is written `(1+t^{a_k})(1+t^{d_k})`
rather than `(1+t^{a_k})(1+t^{2c_k-a_k})`; `fib_d_eq` records that these agree. -/
noncomputable def Efun (t : ℝ) (k : ℕ) : ℝ :=
  (1 + t) * t ^ (Nat.fib (3 * k + 4) - 2) * (1 - t ^ Nat.fib (3 * k + 4))
    / ((1 + t ^ Nat.fib (3 * k + 2)) * (1 + t ^ Nat.fib (3 * k + 5)))

/-- `d_k = 2c_k - a_k`, the write-up's own way of writing the second factor. -/
theorem fib_d_eq (k : ℕ) :
    Nat.fib (3 * k + 5) = 2 * Nat.fib (3 * k + 4) - Nat.fib (3 * k + 2) := by
  have h4 : Nat.fib (3 * k + 4) = Nat.fib (3 * k + 2) + Nat.fib (3 * k + 3) :=
    Nat.fib_add_two
  have h5 : Nat.fib (3 * k + 5) = Nat.fib (3 * k + 3) + Nat.fib (3 * k + 4) :=
    Nat.fib_add_two
  omega

/-- An ODD exponent is what turns `1 - (-t)^m` into `1 + t^m`, and it is the only place the
parity of Fibonacci indices is used. -/
theorem one_sub_neg_pow {t : ℝ} {m : ℕ} (hm : Odd m) : 1 - (-t) ^ m = 1 + t ^ m := by
  rw [hm.neg_pow]
  ring

/-- **`f_{3k+3}(-t) - f_{3k}(-t) = (-1)^k E_k(t)`**, the write-up's exact increment.

Everything above it is algebra over the recurrence; this is where `z = -t` enters, and the
only input beyond the algebra is that `F_{3k+2}`, `F_{3k+4}` and `F_{3k+5}` are odd. -/
theorem increment_eq (t : ℝ) (h0 : 0 < t) (k : ℕ) :
    fapprox (-t) (3 * k + 3) - fapprox (-t) (3 * k) = (-1) ^ k * Efun t k := by
  have ha : Odd (Nat.fib (3 * k + 2)) := fib_odd_of_not_dvd (by omega)
  have hc : Odd (Nat.fib (3 * k + 4)) := fib_odd_of_not_dvd (by omega)
  have hd : Odd (Nat.fib (3 * k + 5)) := fib_odd_of_not_dvd (by omega)
  have h2c : 2 ≤ Nat.fib (3 * k + 4) := by
    have h := two_le_fib (3 * k + 1)
    have he : 3 * k + 1 + 3 = 3 * k + 4 := by omega
    rwa [he] at h
  have hc2 : Odd (Nat.fib (3 * k + 4) - 2) := by
    obtain ⟨j, hj⟩ := hc
    exact ⟨j - 1, by omega⟩
  have hApos : (0 : ℝ) < 1 + t ^ Nat.fib (3 * k + 2) := by positivity
  have hDpos : (0 : ℝ) < 1 + t ^ Nat.fib (3 * k + 5) := by positivity
  have hsign : ((-1 : ℝ)) ^ (3 * k + 1) = -((-1 : ℝ) ^ k) := by
    rw [pow_succ, pow_mul]
    norm_num
  have hnum := triple_closed (-t) (3 * k)
  rw [one_sub_neg_pow ha, one_sub_neg_pow hd, hc.neg_pow, hc2.neg_pow, hsign] at hnum
  simp only [fapprox, show 3 * k + 3 + 1 = 3 * k + 4 from rfl,
    show 3 * k + 3 + 2 = 3 * k + 5 from rfl]
  rw [one_sub_neg_pow ha, one_sub_neg_pow hd,
    div_sub_div _ _ (ne_of_gt hDpos) (ne_of_gt hApos), Efun]
  rw [← mul_div_assoc, div_eq_div_iff (by positivity) (by positivity)]
  linear_combination
    ((1 + t ^ Nat.fib (3 * k + 2)) * (1 + t ^ Nat.fib (3 * k + 5))) * hnum

/-- `f_0(-t) = 1/(1+t)`, the write-up's leading term.  `P_0 = 1` and `L_0 = F_2 = 1`. -/
theorem fapprox_zero (t : ℝ) : fapprox (-t) 0 = 1 / (1 + t) := by
  have h2 : Nat.fib 2 = 1 := by decide
  simp [fapprox, prefixP_one, h2]

/-- **The AM–GM step**, `(1 + t^{c})^2 ≤ (1 + t^{a})(1 + t^{d})`.

The write-up cites AM–GM; the exact certificate is shorter and needs no inequality lemma:
with `s = F_{3k+3}` one has `a = c - s` and `d = c + s`, and
`t^a + t^d - 2t^c = t^a (t^s - 1)^2`. -/
theorem amgm_denom (t : ℝ) (h0 : 0 ≤ t) (k : ℕ) :
    (1 + t ^ Nat.fib (3 * k + 4)) ^ 2
      ≤ (1 + t ^ Nat.fib (3 * k + 2)) * (1 + t ^ Nat.fib (3 * k + 5)) := by
  have h4 : Nat.fib (3 * k + 4) = Nat.fib (3 * k + 2) + Nat.fib (3 * k + 3) :=
    Nat.fib_add_two
  have h5 : Nat.fib (3 * k + 5)
      = Nat.fib (3 * k + 2) + (Nat.fib (3 * k + 3) + Nat.fib (3 * k + 3)) := by
    have h : Nat.fib (3 * k + 5) = Nat.fib (3 * k + 3) + Nat.fib (3 * k + 4) :=
      Nat.fib_add_two
    omega
  rw [h4, h5]
  simp only [pow_add]
  nlinarith [pow_nonneg h0 (Nat.fib (3 * k + 2)), pow_nonneg h0 (Nat.fib (3 * k + 3)),
    sq_nonneg (t ^ Nat.fib (3 * k + 3) - 1),
    mul_nonneg (pow_nonneg h0 (Nat.fib (3 * k + 2)))
      (sq_nonneg (t ^ Nat.fib (3 * k + 3) - 1))]

/-- **The majorant (eq:majorant)**, `E_k(t) ≤ ((1+t)/t²)·g(t^{c_k})`.

It is exactly the AM–GM step plus `t^{c} = t²·t^{c-2}`: both sides have the SAME numerator,
and the inequality is only between the denominators. -/
theorem Efun_le_majorant {t : ℝ} (h0 : 0 < t) (h1 : t < 1) (k : ℕ) :
    Efun t k ≤ (1 + t) / t ^ 2 * gfun (t ^ Nat.fib (3 * k + 4)) := by
  have h2c : 2 ≤ Nat.fib (3 * k + 4) := by
    have h := two_le_fib (3 * k + 1)
    have he : 3 * k + 1 + 3 = 3 * k + 4 := by omega
    rwa [he] at h
  have hpow : t ^ Nat.fib (3 * k + 4) = t ^ 2 * t ^ (Nat.fib (3 * k + 4) - 2) := by
    rw [← pow_add]
    congr 1
    omega
  have hcpos : (0 : ℝ) < t ^ (Nat.fib (3 * k + 4) - 2) := by positivity
  have hone : t ^ Nat.fib (3 * k + 4) ≤ 1 := pow_le_one₀ (le_of_lt h0) (le_of_lt h1)
  have hCpos : (0 : ℝ) < (1 + t ^ Nat.fib (3 * k + 4)) ^ 2 := by positivity
  have hnum : (0 : ℝ)
      ≤ (1 + t) * t ^ (Nat.fib (3 * k + 4) - 2) * (1 - t ^ Nat.fib (3 * k + 4)) :=
    mul_nonneg (mul_nonneg (by linarith) (le_of_lt hcpos)) (by linarith)
  have hrhs : (1 + t) / t ^ 2 * gfun (t ^ Nat.fib (3 * k + 4))
      = (1 + t) * t ^ (Nat.fib (3 * k + 4) - 2) * (1 - t ^ Nat.fib (3 * k + 4))
          / (1 + t ^ Nat.fib (3 * k + 4)) ^ 2 := by
    rw [gfun]
    rw [hpow]
    have ht : (t : ℝ) ≠ 0 := ne_of_gt h0
    field_simp
  rw [Efun, hrhs]
  exact div_le_div_of_nonneg_left hnum hCpos (amgm_denom t (le_of_lt h0) k)

/-- `E_k(t) ≥ 0` on `(0,1)`.  Needed by the assembly, which lower-bounds `C_a(-t)` by
DISCARDING the positive increments -- a step that is only valid if they really are positive. -/
theorem Efun_nonneg {t : ℝ} (h0 : 0 < t) (h1 : t < 1) (k : ℕ) : 0 ≤ Efun t k := by
  have hone : t ^ Nat.fib (3 * k + 4) ≤ 1 := pow_le_one₀ (le_of_lt h0) (le_of_lt h1)
  have hc : (0 : ℝ) < t ^ (Nat.fib (3 * k + 4) - 2) := by positivity
  rw [Efun]
  apply div_nonneg
  · have hsub : (0 : ℝ) ≤ 1 - t ^ Nat.fib (3 * k + 4) := by linarith
    have h1t : (0 : ℝ) ≤ 1 + t := by linarith
    exact mul_nonneg (mul_nonneg h1t (le_of_lt hc)) hsub
  · positivity

/-! ### The assembly, and the carried link restated

This section consumes the telescoping section above and replaces the carried `Prop`.

`fapprox_three_mul` telescopes `increment_eq` from `fapprox_zero`:
`f_{3n}(-t) = 1/(1+t) + ∑_{k<n} (-1)^k E_k(t)`, a finite induction with no analysis in it.
`sum_alt_ge` discards the nonnegative even increments by pairing (`Efun_nonneg`), and
`partial_lower_bound` feeds the odd ones through `Efun_le_majorant` at `k = 2ℓ+1`, where
`c_{2ℓ+1} = F_{6ℓ+7}` is **exactly the module's `fibWitness`** — so
`1/(1+t) - ((1+t)/t²)·∑_{ℓ<m} g(e^{-x_ℓ}) ≤ f_{6m}(-t)`.  With `fib_partial_sum_le`
(i.e. `spacingLemma` at `spaced_fibWitness`) the left side drops to a CONSTANT that is below
every `f_{6m}(-t)`, and a constant below every term of a convergent sequence is below its
limit.

**THE CARRIED LINK IS NOW `PrefixLimit`, NOT `SeriesMajorant`, AND THAT IS A NARROWING.**
`PrefixLimit` says only that the periodic-prefix approximants converge to `C_a` — the single
fact the Fibonacci WORD is needed for, since the `A_n` are increasing prefixes of the fixed
word.  Every quantitative part of the write-up's argument is now proved.

**`SeriesMajorant` is kept, and it is worth saying why it is not what the spine runs on.**
It was narrowed on 2026-09-24 from an inert-existential form to `∃ n` over PARTIAL sums, and
that overshot: subtracting a partial sum instead of the whole one makes the left-hand side
LARGER, so the `∃ n` form is strictly STRONGER than what the consumers need and stronger than
what this route delivers.  It is still TRUE — the partial sums increase to their limit and
the discarded even increments leave strict slack — but proving it needs a tail estimate
(`E_k ≤ 2t^{c_k-2}` with `c_k ≥ k+3`) that nothing else in the row wants.  The route proves
`A(m) ≤ f_{6m}` for every `m`, and passing to the limit yields the constant bound, which is
exactly what `positive_near_one` consumes.  **A narrowing can land on a statement that is
harder than the one it replaced; the check is whether the CONSUMERS got smaller, not whether
the wording did.** -/

/-- The write-up's witness exponent IS a power of `t`: `exp(-x_ℓ) = t^{F_{6ℓ+7}}`. -/
theorem exp_neg_fibWitness {t : ℝ} (h0 : 0 < t) (ℓ : ℕ) :
    exp (-(fibWitness t ℓ)) = t ^ Nat.fib (6 * ℓ + 7) := by
  have hre : -(fibWitness t ℓ) = Real.log (t ^ Nat.fib (6 * ℓ + 7)) := by
    rw [Real.log_pow]
    simp only [fibWitness]
    ring
  rw [hre, Real.exp_log (by positivity)]

/-- The negative increments sit at odd `k`, where `c_k = F_{6ℓ+7}`. -/
theorem fib_index_odd (ℓ : ℕ) : 3 * (2 * ℓ + 1) + 4 = 6 * ℓ + 7 := by ring

/-- **The telescoped partial sum.**  `f_{3n}(-t) = 1/(1+t) + ∑_{k<n} (-1)^k E_k(t)`, from
`fapprox_zero` and `increment_eq`.  No analysis: this is a finite induction. -/
theorem fapprox_three_mul {t : ℝ} (h0 : 0 < t) (n : ℕ) :
    fapprox (-t) (3 * n) = 1 / (1 + t) + ∑ k ∈ Finset.range n, (-1) ^ k * Efun t k := by
  induction n with
  | zero => simpa using fapprox_zero t
  | succ n ih =>
    have hidx : 3 * (n + 1) = 3 * n + 3 := by ring
    have hinc := increment_eq t h0 n
    rw [hidx, Finset.sum_range_succ]
    linarith [ih, hinc]

/-- **Dropping the positive increments.**  Pairing `E_{2ℓ} - E_{2ℓ+1}` and discarding the
nonnegative even terms; this is where `Efun_nonneg` is consumed. -/
theorem sum_alt_ge {t : ℝ} (h0 : 0 < t) (h1 : t < 1) (m : ℕ) :
    -(∑ ℓ ∈ Finset.range m, Efun t (2 * ℓ + 1))
      ≤ ∑ k ∈ Finset.range (2 * m), (-1) ^ k * Efun t k := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hidx : 2 * (m + 1) = 2 * m + 1 + 1 := by ring
    have he : ((-1 : ℝ)) ^ (2 * m) = 1 := by
      rw [pow_mul]; norm_num
    have ho : ((-1 : ℝ)) ^ (2 * m + 1) = -1 := by
      rw [pow_succ, he]; ring
    rw [Finset.sum_range_succ, hidx, Finset.sum_range_succ, Finset.sum_range_succ, he, ho]
    have hpos := Efun_nonneg h0 h1 (2 * m)
    linarith

/-- **The finite lower bound**, and the step that consumes the whole telescoping section:
`1/(1+t) - ((1+t)/t²)·∑_{ℓ<m} g(e^{-x_ℓ}) ≤ f_{6m}(-t)`. -/
theorem partial_lower_bound {t : ℝ} (h0 : 0 < t) (h1 : t < 1) (m : ℕ) :
    1 / (1 + t)
        - (1 + t) / t ^ 2 * (∑ ℓ ∈ Finset.range m, gfun (exp (-(fibWitness t ℓ))))
      ≤ fapprox (-t) (6 * m) := by
  have hidx : 6 * m = 3 * (2 * m) := by ring
  have hmaj : ∑ ℓ ∈ Finset.range m, Efun t (2 * ℓ + 1)
      ≤ (1 + t) / t ^ 2 * ∑ ℓ ∈ Finset.range m, gfun (exp (-(fibWitness t ℓ))) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun ℓ _ => ?_)
    have h := Efun_le_majorant h0 h1 (2 * ℓ + 1)
    rw [fib_index_odd ℓ] at h
    rwa [exp_neg_fibWitness h0 ℓ]
  have halt := sum_alt_ge h0 h1 m
  rw [hidx, fapprox_three_mul h0 (2 * m)]
  linarith

/-- The constant `1/(1+t) - ((1+t)/t²)·(127/600)` is below EVERY `f_{6m}(-t)`.  This is
where `spacingLemma` and `spaced_fibWitness` enter, through `fib_partial_sum_le`. -/
theorem const_le_fapprox {t : ℝ} (h0 : 0 < t) (h1 : t < 1) (m : ℕ) :
    1 / (1 + t) - (1 + t) / t ^ 2 * (127 / 600) ≤ fapprox (-t) (6 * m) := by
  have hc : (0 : ℝ) < (1 + t) / t ^ 2 := by positivity
  have hsum := fib_partial_sum_le h0 h1 m
  have h := partial_lower_bound h0 h1 m
  nlinarith

/-- **The carried link, restated as a pure CONVERGENCE statement.**

This replaces `SeriesMajorant`.  It is the one thing the Fibonacci word is needed for: the
periodic-prefix approximants `f_n(z) = P_n(z)/(1 - z^{L_n})` converge to `C_a(z)`, because
the `A_n` are increasing prefixes of the fixed word.  Everything else the write-up's
argument does is now proved. -/
def PrefixLimit (Ca : ℝ → ℝ) : Prop :=
  ∀ t : ℝ, 0 < t → t < 1 →
    Filter.Tendsto (fun n => fapprox (-t) n) Filter.atTop (nhds (Ca (-t)))

theorem tendsto_six_mul {t : ℝ} {Ca : ℝ → ℝ} (h : PrefixLimit Ca) (h0 : 0 < t) (h1 : t < 1) :
    Filter.Tendsto (fun m => fapprox (-t) (6 * m)) Filter.atTop (nhds (Ca (-t))) :=
  (h t h0 h1).comp
    (Filter.tendsto_atTop_atTop_of_monotone (fun a b hab => by omega) (fun b => ⟨b, by omega⟩))

/-- **`SeriesMajorantOld` follows from the convergence interface alone.**  A constant below
every term of a convergent sequence is below its limit. -/
theorem seriesMajorantOld_of_prefixLimit (Ca : ℝ → ℝ) (h : PrefixLimit Ca) :
    SeriesMajorantOld Ca := by
  intro t h9 h1
  have h0 : (0 : ℝ) < t := by linarith
  refine ⟨fun ℓ => (16 : ℝ) ^ ℓ, spaced_pow_sixteen, ?_⟩
  exact ge_of_tendsto' (tendsto_six_mul h h0 h1) (fun m => const_le_fapprox h0 h1 m)

/-- **The negative half, from the convergence interface.** -/
theorem positive_near_one_of_prefixLimit (Ca : ℝ → ℝ) (h : PrefixLimit Ca)
    (t : ℝ) (h9 : 9 / 10 ≤ t) (h1 : t < 1) : 0 < Ca (-t) := by
  have h0 : (0 : ℝ) < t := by linarith
  have h1t : (0 : ℝ) < 1 + t := by linarith
  have ht2 : (0 : ℝ) < t ^ 2 := by positivity
  have hkey : 0 < 1 / (1 + t) - (1 + t) / t ^ 2 * (127 / 600) := by
    have e : 1 / (1 + t) - (1 + t) / t ^ 2 * (127 / 600)
        = (600 * t ^ 2 - 127 * (1 + t) ^ 2) / (600 * t ^ 2 * (1 + t)) := by
      field_simp
    rw [e]
    apply div_pos _ (by positivity)
    nlinarith [sq_nonneg (t - 1), sq_nonneg (t - 9 / 10)]
  have hbound := ge_of_tendsto' (tendsto_six_mul h h0 h1)
    (fun m => const_le_fapprox h0 h1 m)
  linarith

/-! ### The Fibonacci word, and `PrefixLimit` DISCHARGED

**The last carried link of this row is gone, and `C_a` is now a DEFINED object rather than
an abstract one.**

The chain, and why each piece is here rather than assumed:

* `fibWord` is the concatenation recurrence `A_{n+2} = A_{n+1} A_n`, and `subst_fibWord`
  proves `A_{n+1} = σ(A_n)` for the actual substitution `σ(a) = ab`, `σ(b) = a`
  (`fibWord_eq_iterate` states it as `A_n = σ^n(a)`, the write-up's own sentence).
  `fibWord_five` pins the printed prefix against the source's `w = abaababa…`.  Three
  independent anchors, because the object is ours and the theorem is the source's.
* **`prefixP_eq_wordCount` is the Python positive control, as a theorem.**
  `verify_360139_telescope.py` check (1) compares the recurrence with the word's prefix
  counts for `n = 0..16`; that check existed because the reframing replaced the source's
  object by a different one and no theorem about the recurrence could see the difference.
  It is now proved for every `n`, and the check is a regression test rather than the
  argument.
* `fibSeq` reads position `j` off `A_j`, well defined because the words form a prefix chain
  (`fibWord_prefix_mono`) and `le_fib_succ` makes them long enough; `CaFib` is the
  generating function of its `a`-positions, i.e. the write-up's `C_a`.
* `prefixLimit_CaFib` **discharges `PrefixLimit`**: `P_n` is the partial sum over the first
  `L_n` positions (`prefixP_eq_partialSum`), the series is summable for `|z| < 1`, `L_n → ∞`,
  and `z^{L_n} → 0`, so `f_n(z) → C_a(z)`.

## What this row now proves, and what it does NOT

The source's Conjecture 5.12 is `C_a(x) > 0` for every `x ∈ (-1,1)`.  Proved here,
unconditionally:

* `positive_of_nonneg` — `x ∈ [0,1)`, in fact `C_a(x) ≥ 1`.  This became free the moment
  `C_a` stopped being an abstract hypothesis: every coefficient is `0` or `1` and the
  constant one is `1`.
* `positive_near_one_fib` — `x = -t` with `9/10 ≤ t < 1`, the telescoping argument.

**NOT proved here: `x ∈ (-9/10, 0)`.**  The write-up handles that compact interval by a
separate `w = σ³(w)` even-block decomposition, and this module does not formalise it.  So
the module carries NOTHING and is still not the whole theorem — a distinction worth keeping
separate from "carries a hypothesis", because the two fail for different reasons and only
one of them is a gap in an argument. -/

/-- The substitution words of `σ(a) = ab`, `σ(b) = a`, indexed so that `fibWord (n+1)` is
the write-up's `A_n` and `fibWord 0` is its `A_{-1} = b`.  `true` is the letter `a`. -/
def fibWord : ℕ → List Bool
  | 0 => [false]
  | 1 => [true]
  | (n + 2) => fibWord (n + 1) ++ fibWord n

theorem fibWord_zero : fibWord 0 = [false] := rfl

theorem fibWord_one : fibWord 1 = [true] := rfl

theorem fibWord_add_two (n : ℕ) : fibWord (n + 2) = fibWord (n + 1) ++ fibWord n := rfl

/-- `|A_n| = L_n = F_{n+2}`, in the shifted indexing `|fibWord n| = F_{n+1}`. -/
theorem fibWord_length (n : ℕ) : (fibWord n).length = Nat.fib (n + 1) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => rfl
    | 1 => rfl
    | (m + 2) =>
      have hfib : Nat.fib (m + 2 + 1) = Nat.fib (m + 1) + Nat.fib (m + 1 + 1) :=
        Nat.fib_add_two
      rw [fibWord_add_two, List.length_append, ih (m + 1) (by omega), ih m (by omega), hfib]
      omega

/-- **The generating polynomial of the `a`-positions**, in Horner form. -/
noncomputable def wordCount (z : ℝ) : List Bool → ℝ
  | [] => 0
  | (c :: w) => (if c then 1 else 0) + z * wordCount z w

theorem wordCount_nil (z : ℝ) : wordCount z [] = 0 := rfl

theorem wordCount_cons (z : ℝ) (c : Bool) (w : List Bool) :
    wordCount z (c :: w) = (if c then 1 else 0) + z * wordCount z w := rfl

theorem getD_cons_succ (c : Bool) (w : List Bool) (j : ℕ) :
    (c :: w).getD (j + 1) false = w.getD j false := rfl

/-- Horner form is the sum it is meant to be: `∑_{j < |w|} [w_j = a]·z^j`. -/
theorem wordCount_eq_sum (z : ℝ) (w : List Bool) :
    wordCount z w = ∑ j ∈ Finset.range w.length, if w.getD j false then z ^ j else 0 := by
  induction w with
  | nil => simp [wordCount_nil]
  | cons c w ih =>
    have hterm : ∀ j : ℕ, z * (if w.getD j false then z ^ j else 0)
        = if (c :: w).getD (j + 1) false then z ^ (j + 1) else 0 := by
      intro j
      rw [getD_cons_succ]
      by_cases h : w.getD j false
      · rw [if_pos h, if_pos h, pow_succ]
        ring
      · rw [if_neg h, if_neg h, mul_zero]
    rw [wordCount_cons, ih, List.length_cons, Finset.sum_range_succ', Finset.mul_sum,
      Finset.sum_congr rfl (fun j _ => hterm j)]
    have hzero : (c :: w).getD 0 false = c := rfl
    rw [hzero, pow_zero, add_comm]

/-- **Concatenation shifts by the length of the first word.**  This is the whole reason the
recurrence `P_{n+1} = P_n + z^{L_n} P_{n-1}` holds. -/
theorem wordCount_append (z : ℝ) (u v : List Bool) :
    wordCount z (u ++ v) = wordCount z u + z ^ u.length * wordCount z v := by
  induction u with
  | nil => simp [wordCount_nil]
  | cons c u ih =>
    rw [List.cons_append, wordCount_cons, wordCount_cons, ih, List.length_cons, pow_succ]
    ring

/-- **THE POSITIVE CONTROL, AS A THEOREM.**  The recurrence really does count the word.

`verify_360139_telescope.py` check (1) builds the Fibonacci word by substitution and
compares its prefix counts with `prefixP` for `n = 0..16`.  That check exists because the
reframing replaced the source's object (prefix counts of the word) by a different one (the
recurrence), and no theorem about the recurrence can see whether the two agree.  This is
that agreement, for every `n`. -/
theorem prefixP_eq_wordCount (z : ℝ) (n : ℕ) : prefixP z n = wordCount z (fibWord n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp [prefixP_zero, fibWord_zero, wordCount_cons, wordCount_nil]
    | 1 => simp [prefixP_one, fibWord_one, wordCount_cons, wordCount_nil]
    | (m + 2) =>
      rw [prefixP_succ_succ, fibWord_add_two, wordCount_append, fibWord_length,
        ih (m + 1) (by omega), ih m (by omega)]

/-- The substitution words form a PREFIX CHAIN, which is what makes them approximants of a
single infinite word.  Immediate from `A_{n+2} = A_{n+1} A_n`. -/
theorem fibWord_prefix (n : ℕ) : fibWord (n + 1) <+: fibWord (n + 2) :=
  ⟨fibWord n, (fibWord_add_two n).symm⟩

/-- The substitution `σ(a) = ab`, `σ(b) = a`, as a map on words (`true` is `a`). -/
def subst : List Bool → List Bool
  | [] => []
  | (true :: w) => true :: false :: subst w
  | (false :: w) => true :: subst w

theorem subst_nil : subst [] = [] := rfl

theorem subst_cons_true (w : List Bool) :
    subst (true :: w) = true :: false :: subst w := rfl

theorem subst_cons_false (w : List Bool) : subst (false :: w) = true :: subst w := rfl

/-- `σ` is a morphism of words. -/
theorem subst_append (u v : List Bool) : subst (u ++ v) = subst u ++ subst v := by
  induction u with
  | nil => simp [subst_nil]
  | cons c u ih =>
    cases c
    · rw [List.cons_append, subst_cons_false, subst_cons_false, ih, List.cons_append]
    · rw [List.cons_append, subst_cons_true, subst_cons_true, ih, List.cons_append,
        List.cons_append]

/-- **`A_{n+1} = σ(A_n)`, so `A_n = σ^n(a)` — the write-up's own description of these
words.**  This is what ties `fibWord`, defined by the concatenation recurrence, to the
SUBSTITUTION the problem is about. -/
theorem subst_fibWord (n : ℕ) : subst (fibWord n) = fibWord (n + 1) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => rfl
    | 1 => rfl
    | (m + 2) =>
      rw [fibWord_add_two, subst_append, ih (m + 1) (by omega), ih m (by omega)]
      exact (fibWord_add_two (m + 1)).symm

/-- `A_n = σ^n(A_0) = σ^n([a])`, stated with an explicit iterate. -/
theorem fibWord_eq_iterate (n : ℕ) : fibWord (n + 1) = subst^[n] (fibWord 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ← ih, subst_fibWord]

/-! ### The infinite word, and `PrefixLimit` DISCHARGED -/

/-- `n ≤ F_{n+1}`, which is what makes the word long enough at every position. -/
theorem le_fib_succ (n : ℕ) : n ≤ Nat.fib (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h : Nat.fib (n + 1 + 1) = Nat.fib n + Nat.fib (n + 1) := Nat.fib_add_two
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · decide
    · have h1 : 1 ≤ Nat.fib n := Nat.fib_pos.mpr hpos
      omega

/-- From index `1` on, each word is a prefix of the next. -/
theorem fibWord_prefix_succ {m : ℕ} (h : 1 ≤ m) : fibWord m <+: fibWord (m + 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  exact ⟨fibWord k, (fibWord_add_two k).symm⟩

theorem fibWord_prefix_add {n : ℕ} (h1 : 1 ≤ n) (k : ℕ) :
    fibWord n <+: fibWord (n + k) := by
  induction k with
  | zero => exact List.prefix_rfl
  | succ k ih => exact ih.trans (fibWord_prefix_succ (by omega))

theorem fibWord_prefix_mono {n m : ℕ} (h1 : 1 ≤ n) (h : n ≤ m) :
    fibWord n <+: fibWord m := by
  obtain ⟨k, rfl⟩ : ∃ k, m = n + k := ⟨m - n, by omega⟩
  exact fibWord_prefix_add h1 k

/-- **The infinite fixed word.**  Position `j` is read off `A_j`, which is long enough by
`le_fib_succ`; `fibSeq_eq_getD` says every later word gives the same answer. -/
def fibSeq (j : ℕ) : Bool := (fibWord (j + 1)).getD j false

theorem fibSeq_eq_getD {n j : ℕ} (h1 : 1 ≤ n) (hj : j < Nat.fib (n + 1)) :
    (fibWord n).getD j false = fibSeq j := by
  have hjlen : j < (fibWord (j + 1)).length := by
    rw [fibWord_length]
    have h := le_fib_succ (j + 1)
    omega
  have hnlen : j < (fibWord n).length := by rw [fibWord_length]; exact hj
  obtain ⟨u, hu⟩ := fibWord_prefix_mono h1 (le_max_left n (j + 1))
  obtain ⟨v, hv⟩ := fibWord_prefix_mono (n := j + 1) (by omega) (le_max_right n (j + 1))
  have e1 : (fibWord n).getD j false = (fibWord (max n (j + 1))).getD j false := by
    rw [← hu, List.getD_append _ _ _ _ hnlen]
  have e2 : (fibWord (j + 1)).getD j false = (fibWord (max n (j + 1))).getD j false := by
    rw [← hv, List.getD_append _ _ _ _ hjlen]
  show (fibWord n).getD j false = (fibWord (j + 1)).getD j false
  rw [e1, e2]

/-- `P_n` is the partial sum of the fixed word's generating series over the first `L_n`
positions. -/
theorem prefixP_eq_partialSum (z : ℝ) {n : ℕ} (h1 : 1 ≤ n) :
    prefixP z n = ∑ j ∈ Finset.range (Nat.fib (n + 1)), if fibSeq j then z ^ j else 0 := by
  rw [prefixP_eq_wordCount, wordCount_eq_sum, fibWord_length]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  rw [fibSeq_eq_getD h1 (Finset.mem_range.mp hj)]

/-- **`C_a`, defined**: the generating function of the `a`-positions of the fixed word. -/
noncomputable def CaFib (z : ℝ) : ℝ := ∑' j : ℕ, if fibSeq j then z ^ j else 0

theorem summable_fibSeq {z : ℝ} (hz : |z| < 1) :
    Summable (fun j : ℕ => if fibSeq j then z ^ j else 0) := by
  refine Summable.of_norm_bounded
    (summable_geometric_of_lt_one (abs_nonneg z) hz) (fun j => ?_)
  by_cases h : fibSeq j
  · simp [h]
  · simp [h, pow_nonneg (abs_nonneg z) j]

theorem tendsto_fib_succ : Filter.Tendsto (fun n : ℕ => Nat.fib (n + 1))
    Filter.atTop Filter.atTop :=
  Filter.tendsto_atTop_mono le_fib_succ Filter.tendsto_id

theorem tendsto_fib_add_two : Filter.Tendsto (fun n : ℕ => Nat.fib (n + 2))
    Filter.atTop Filter.atTop :=
  Filter.tendsto_atTop_mono (fun n => (le_fib_succ n).trans
    (Nat.fib_mono (by omega))) Filter.tendsto_id

theorem tendsto_prefixP {z : ℝ} (hz : |z| < 1) :
    Filter.Tendsto (fun n => prefixP z n) Filter.atTop (nhds (CaFib z)) := by
  have hpart : Filter.Tendsto
      (fun N => ∑ j ∈ Finset.range N, if fibSeq j then z ^ j else 0)
      Filter.atTop (nhds (CaFib z)) := (summable_fibSeq hz).hasSum.tendsto_sum_nat
  refine Filter.Tendsto.congr' ?_ (hpart.comp tendsto_fib_succ)
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  exact (prefixP_eq_partialSum z hn).symm

theorem tendsto_fapprox {z : ℝ} (hz : |z| < 1) :
    Filter.Tendsto (fun n => fapprox z n) Filter.atTop (nhds (CaFib z)) := by
  have hnum : Filter.Tendsto (fun n => prefixP z (n + 1)) Filter.atTop (nhds (CaFib z)) :=
    (tendsto_prefixP hz).comp (Filter.tendsto_add_atTop_nat 1)
  have hz' : ‖z‖ < 1 := by rwa [Real.norm_eq_abs]
  have hpow : Filter.Tendsto (fun n => z ^ Nat.fib (n + 2)) Filter.atTop (nhds 0) :=
    (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hz').comp tendsto_fib_add_two
  have hden : Filter.Tendsto (fun n => 1 - z ^ Nat.fib (n + 2)) Filter.atTop (nhds 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hpow
  have hdiv := hnum.div hden one_ne_zero
  simpa [fapprox, Pi.div_def] using hdiv

/-- **`PrefixLimit` DISCHARGED.**  The last carried link of this row: the periodic-prefix
approximants converge to the generating function of the fixed word. -/
theorem prefixLimit_CaFib : PrefixLimit CaFib := by
  intro t h0 h1
  refine tendsto_fapprox ?_
  rw [abs_lt]
  constructor <;> linarith

/-- **Conjecture 5.12 on `[9/10, 1)`, unconditionally.** -/
theorem positive_near_one_fib (t : ℝ) (h9 : 9 / 10 ≤ t) (h1 : t < 1) : 0 < CaFib (-t) :=
  positive_near_one_of_prefixLimit CaFib prefixLimit_CaFib t h9 h1

theorem fibSeq_zero : fibSeq 0 = true := rfl

/-- **The word is the write-up's own `w = abaababa…`.**  A faithfulness anchor: `fibWord` is
defined by the concatenation recurrence, `subst_fibWord` ties it to the substitution, and
this pins its printed prefix against the one the source writes down. -/
theorem fibWord_five :
    fibWord 5 = [true, false, true, true, false, true, false, true] := by decide

/-- **The nonnegative half of Conjecture 5.12, now that `C_a` is a DEFINED object.**  Every
coefficient is `0` or `1` and the constant one is `1`, so `C_a(z) ≥ 1` on `[0,1)`.  This was
free only because the limit is no longer an abstract hypothesis. -/
theorem one_le_CaFib {z : ℝ} (h0 : 0 ≤ z) (h1 : z < 1) : 1 ≤ CaFib z := by
  have habs : |z| < 1 := by rwa [abs_of_nonneg h0]
  have hnn : ∀ j : ℕ, j ∉ ({0} : Finset ℕ) →
      0 ≤ (if fibSeq j then z ^ j else 0) := by
    intro j _
    by_cases h : fibSeq j
    · rw [if_pos h]; positivity
    · rw [if_neg h]
  have h := (summable_fibSeq habs).sum_le_tsum {0} hnn
  simpa [CaFib, fibSeq_zero] using h

theorem positive_of_nonneg (z : ℝ) (h0 : 0 ≤ z) (h1 : z < 1) : 0 < CaFib z :=
  lt_of_lt_of_le zero_lt_one (one_le_CaFib h0 h1)

/-! ### Widening the covered set, and naming the band that is left

Two bounds of very different character, and each one's threshold is now what the BOUND
gives rather than a number the write-up rounded to.

* **`positive_of_six_sevenths`** — the telescoping bound
  `1/(1+t) - ((1+t)/t²)(127/600)` is positive exactly when `473t² - 254t - 127 > 0`, i.e.
  for `t > 0.85210…`.  The module previously stopped at `9/10`; `6/7` works, with `137/49`
  of slack in the numerator, and `17/20` does not.  `lower_bound_of_prefixLimit` is the same
  bound with the range restriction dropped entirely — the argument never needed one.
* **`positive_of_small`** — discard every even term and bound each odd one by `-t^j`:
  `C_a(-t) ≥ 1 - t/(1-t)`, positive exactly for `t < 1/2`, and EXACTLY zero at `1/2`.

`positive_of_mem` states the union: **`C_a(x) > 0` on `(-1, -6/7] ∪ (-1/2, 1)`**.

## The band `[-6/7, -1/2]`, and what closing it costs

It is uncovered because both bounds are out of range there, **not because `C_a` comes near
zero**: `verify_360139_coverage.py` check (4) puts `C_a(-t) ≥ 0.562` throughout it.  The gap
is in the ARGUMENT, not the theorem.

Check (5) of the same script prices the obvious repair.  Truncating the series at `N` and
bounding the tail by `t^N/(1-t)` needs `(1-t)·S_N(t) - t^N > 0` on the band; the smallest
`N` that clears it is **18**, with margin `+0.0055` at the right endpoint, and the resulting
degree-19 polynomial has coefficients

    [1, -1, 1, -2, 1, -1, 1, -1, 2, -1, 1, -2, 1, -1, 1, -1, 2, -1, -1].

**The natural pair grouping `t^{2i}(c_{2i} + c_{2i+1} t)` does NOT work**, because pairs of
the form `(1, -2)` occur and `1 - 2t` is negative on most of the band.  So the repair is a
genuine degree-19 positivity, not a one-liner — which is worth recording before the next
attempt starts, rather than discovered halfway through it. -/

/-- The telescoping lower bound with NO range restriction beyond `0 < t < 1`.  The `9/10`
in `SeriesMajorantOld` was a range the write-up chose, not one the argument needs. -/
theorem lower_bound_of_prefixLimit (Ca : ℝ → ℝ) (h : PrefixLimit Ca) {t : ℝ}
    (h0 : 0 < t) (h1 : t < 1) :
    1 / (1 + t) - (1 + t) / t ^ 2 * (127 / 600) ≤ Ca (-t) :=
  ge_of_tendsto' (tendsto_six_mul h h0 h1) (fun m => const_le_fapprox h0 h1 m)

/-- **The telescoping half reaches down to `6/7`, not just `9/10`.**

The bound `1/(1+t) - ((1+t)/t²)(127/600)` is positive exactly when
`600t² - 127(1+t)² = 473t² - 254t - 127 > 0`, i.e. for `t > 0.85210…`.  `9/10` was the
write-up's round number; at `6/7` the numerator still has `137/49` of slack, and at `17/20`
it is already negative. -/
theorem positive_of_six_sevenths (t : ℝ) (h : 6 / 7 ≤ t) (h1 : t < 1) : 0 < CaFib (-t) := by
  have h0 : (0 : ℝ) < t := by linarith
  have h1t : (0 : ℝ) < 1 + t := by linarith
  have ht2 : (0 : ℝ) < t ^ 2 := by positivity
  have hkey : 0 < 1 / (1 + t) - (1 + t) / t ^ 2 * (127 / 600) := by
    have e : 1 / (1 + t) - (1 + t) / t ^ 2 * (127 / 600)
        = (600 * t ^ 2 - 127 * (1 + t) ^ 2) / (600 * t ^ 2 * (1 + t)) := by
      field_simp
    rw [e]
    apply div_pos _ (by positivity)
    nlinarith [sq_nonneg (t - 6 / 7)]
  have hb := lower_bound_of_prefixLimit CaFib prefixLimit_CaFib h0 h1
  linarith

/-! ### The crude bound, for small `t` -/

theorem shiftGeom_summable {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    Summable (fun b : ℕ => -(t ^ (b + 1))) := by
  have hbase : Summable (fun b : ℕ => t * t ^ b) :=
    (summable_geometric_of_lt_one (le_of_lt h0) h1).mul_left t
  have hfun : (fun b : ℕ => -(t ^ (b + 1))) = fun b : ℕ => -(t * t ^ b) := by
    funext b
    rw [pow_succ]
    ring
  rw [hfun]
  exact hbase.neg

theorem shiftGeom_tsum {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    ∑' b : ℕ, -(t ^ (b + 1)) = -(t / (1 - t)) := by
  have hfun : (fun b : ℕ => -(t ^ (b + 1))) = fun b : ℕ => -(t * t ^ b) := by
    funext b
    rw [pow_succ]
    ring
  rw [hfun, tsum_neg, tsum_mul_left, tsum_geometric_of_lt_one (le_of_lt h0) h1]
  have : (1 : ℝ) - t ≠ 0 := by linarith
  field_simp

/-- Every coefficient is `0` or `1`, so every term is at least `-t^j`. -/
theorem term_ge_neg_pow {t : ℝ} (h0 : 0 < t) (j : ℕ) :
    -(t ^ j) ≤ (if fibSeq j then (-t) ^ j else 0) := by
  have hpow : |(-t) ^ j| = t ^ j := by
    rw [abs_pow, abs_neg, abs_of_pos h0]
  by_cases hb : fibSeq j
  · rw [if_pos hb]
    have hna := neg_abs_le ((-t) ^ j)
    rw [hpow] at hna
    exact hna
  · rw [if_neg hb]
    have : (0 : ℝ) ≤ t ^ j := by positivity
    linarith

theorem abs_neg_lt_one {t : ℝ} (h0 : 0 < t) (h1 : t < 1) : |(-t)| < 1 := by
  rw [abs_neg, abs_of_pos h0]
  exact h1

/-- Peel the constant term: `C_a(-t) = 1 + ∑_{b} [w_{b+1}](-t)^{b+1}`. -/
theorem CaFib_split {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    CaFib (-t) = 1 + ∑' b : ℕ, (if fibSeq (b + 1) then (-t) ^ (b + 1) else 0) := by
  have hg := summable_fibSeq (abs_neg_lt_one h0 h1)
  rw [CaFib, hg.tsum_eq_zero_add]
  -- `congr 1` closes both sides: the `0`th term reduces to `1` because `fibSeq 0 = true`.
  congr 1

theorem CaFib_tail_ge {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    -(t / (1 - t)) ≤ ∑' b : ℕ, (if fibSeq (b + 1) then (-t) ^ (b + 1) else 0) := by
  have hg := summable_fibSeq (abs_neg_lt_one h0 h1)
  -- **Supply `f` explicitly.**  Left implicit, `summable_nat_add_iff` makes Lean guess a
  -- function from `f (n+1)`, and that higher-order unification is what blew the heartbeat
  -- budget on the first two drafts of this proof.
  have hshift : Summable (fun b : ℕ => if fibSeq (b + 1) then (-t) ^ (b + 1) else 0) :=
    (_root_.summable_nat_add_iff
      (f := fun j : ℕ => if fibSeq j then (-t) ^ j else 0) 1).mpr hg
  have hsum_le : ∑' b : ℕ, -(t ^ (b + 1))
      ≤ ∑' b : ℕ, (if fibSeq (b + 1) then (-t) ^ (b + 1) else 0) :=
    (shiftGeom_summable h0 h1).tsum_le_tsum
      (fun b => term_ge_neg_pow h0 (b + 1)) hshift
  rwa [shiftGeom_tsum h0 h1] at hsum_le

/-- `C_a(-t) ≥ 1 - t/(1-t)`: the first term is exactly `1` and every later one is at least
`-t^j`.  Crude on purpose — every even term is thrown away. -/
theorem CaFib_ge_crude {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    1 - t / (1 - t) ≤ CaFib (-t) := by
  have hs := CaFib_split h0 h1
  have ht := CaFib_tail_ge h0 h1
  rw [hs]
  linarith

/-- **The small-`t` half.**  `1 - t/(1-t) > 0` exactly for `t < 1/2`, and it is EXACTLY zero
at `t = 1/2` — so `1/2` is what this bound gives, not a round number. -/
theorem positive_of_small (t : ℝ) (h0 : 0 < t) (h : t < 1 / 2) : 0 < CaFib (-t) := by
  have h1 : t < 1 := by linarith
  have hpos : (0 : ℝ) < 1 - t := by linarith
  have hb := CaFib_ge_crude h0 h1
  have hgt : 0 < 1 - t / (1 - t) := by
    rw [sub_pos, div_lt_one hpos]
    linarith
  linarith

/-- **The covered set, in one statement.**  `C_a(x) > 0` on `(-1, -6/7] ∪ (-1/2, 1)`.

The source's Conjecture 5.12 is all of `(-1,1)`; the band `[-6/7, -1/2]` is NOT covered
here, because both bounds are out of range there — not because `C_a` comes near zero, which
`verify_360139_coverage.py` check (4) puts above `0.56` throughout the band. -/
theorem positive_of_mem {x : ℝ}
    (h : x ∈ Set.Ioc (-1 : ℝ) (-(6 / 7)) ∪ Set.Ioo (-(1 / 2) : ℝ) 1) : 0 < CaFib x := by
  have hx : x = -(-x) := by ring
  rcases h with ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩
  · rw [hx]
    exact positive_of_six_sevenths (-x) (by linarith) (by linarith)
  · by_cases hx0 : 0 ≤ x
    · exact positive_of_nonneg x hx0 hhi
    · rw [hx]
      exact positive_of_small (-x) (by linarith) (by linarith)

/-! ### The band `[1/2, 6/7]`, and Conjecture 5.12 on all of `(-1,1)`

**Keeping the even terms is what makes this cheap.**  Truncating at `N` and bounding the
tail by `t^N/(1-t)` throws away the sign pattern and needs `N = 18`, leaving a degree-19
polynomial with margin `0.0055`.  The even-index terms are NONNEGATIVE, so the tail really
costs only `t^{N+1}/(1-t²)` — and that needs `N = 12`, leaving

    (1 - t²)·S_12(t) - t^13 = 1 - t³ - t⁴ + t⁸ + t⁹ - t¹¹ - t¹²

with margin `0.0308` on the band.  Six times the room and seven degrees less; `nlinarith`
takes it with the obvious hints.  `verify_360139_coverage.py` checks both routes side by
side (checks 6–8), the closed form of `S_12` (check 5) and the identity above (check 7).

**The parity split is written as an algebraic identity, not a case analysis.**  The odd-index
indicator is `(t^b - (-t)^b)/2`, which turns the tail into two ordinary geometric series and
avoids reindexing the odd positions entirely.

`positive_on_band` closes `[1/2, 6/7]`; with `positive_of_small` and
`positive_of_six_sevenths` the three regimes meet, and **`conjecture_5_12` is the source's
theorem on its whole interval**.

## What this row now claims

`C_a(x) > 0` for every `x ∈ (-1,1)`, unconditionally, where `C_a = CaFib` is the generating
function of the `a`-positions of the Fibonacci fixed word.  Nothing is carried.  The object
is tied to the source by three anchors — the concatenation recurrence, `subst_fibWord`
(`A_{n+1} = σ(A_n)`, hence `A_n = σⁿ(a)`) and `fibWord_five` (`w = abaababa…`).  The
write-up's Tasks 2–5 are explicitly *"questions for further work, not additional solved
claims"*, and its Theorem 1 is the single statement above, so this is the whole of it. -/

/-- The first thirteen letters, which is enough to read positions `0 … 11`. -/
theorem fibWord_six :
    fibWord 6 = [true, false, true, true, false, true, false, true, true, false, true,
      true, false] := by decide

theorem fibSeq_eq_six (j : ℕ) (hj : j < 12) : fibSeq j = (fibWord 6).getD j false := by
  -- `omega` treats `Nat.fib 7` and `Nat.fib (6 + 1)` as two atoms: state it as the goal does.
  have h13 : Nat.fib (6 + 1) = 13 := by decide
  exact (fibSeq_eq_getD (n := 6) (by omega) (by omega)).symm

/-- The truncated series at `N = 12`, written out. -/
theorem sum_twelve (t : ℝ) :
    ∑ j ∈ Finset.range 12, (if fibSeq j then (-t) ^ j else 0)
      = 1 + t ^ 2 - t ^ 3 - t ^ 5 - t ^ 7 + t ^ 8 + t ^ 10 - t ^ 11 := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero,
    fibSeq_eq_six 0 (by norm_num), fibSeq_eq_six 1 (by norm_num),
    fibSeq_eq_six 2 (by norm_num), fibSeq_eq_six 3 (by norm_num),
    fibSeq_eq_six 4 (by norm_num), fibSeq_eq_six 5 (by norm_num),
    fibSeq_eq_six 6 (by norm_num), fibSeq_eq_six 7 (by norm_num),
    fibSeq_eq_six 8 (by norm_num), fibSeq_eq_six 9 (by norm_num),
    fibSeq_eq_six 10 (by norm_num), fibSeq_eq_six 11 (by norm_num), fibWord_six]
  norm_num
  ring

/-! ### The tail from index 12, with the EVEN terms kept

The crude bound throws away the sign pattern and pays `t^N/(1-t)`.  Keeping the even terms
— which are nonnegative — pays only `t^{N+1}/(1-t²)`, and that halves the tail.  It is the
difference between needing `N = 18` and needing `N = 12`.

The odd-index indicator is written `(t^b - (-t)^b)/2`, which turns the parity split into two
ordinary geometric series and avoids reindexing entirely. -/

theorem negGeom_summable {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    Summable (fun b : ℕ => (-t) ^ b) := by
  refine summable_geometric_of_norm_lt_one ?_
  rw [Real.norm_eq_abs, abs_neg, abs_of_pos h0]
  exact h1

theorem negGeom_tsum {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    ∑' b : ℕ, (-t) ^ b = (1 + t)⁻¹ := by
  have hnorm : ‖(-t)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_neg, abs_of_pos h0]
    exact h1
  rw [tsum_geometric_of_norm_lt_one hnorm]
  congr 1
  ring

theorem oddPart_summable {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    Summable (fun b : ℕ => -(t ^ 12 * (t ^ b - (-t) ^ b) / 2)) := by
  have ht : Summable (fun b : ℕ => t ^ b) := summable_geometric_of_lt_one (le_of_lt h0) h1
  exact (((ht.sub (negGeom_summable h0 h1)).mul_left (t ^ 12)).div_const 2).neg

theorem oddPart_tsum {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    ∑' b : ℕ, -(t ^ 12 * (t ^ b - (-t) ^ b) / 2) = -(t ^ 13 / (1 - t ^ 2)) := by
  have ht : Summable (fun b : ℕ => t ^ b) := summable_geometric_of_lt_one (le_of_lt h0) h1
  have hn := negGeom_summable h0 h1
  rw [tsum_neg, tsum_div_const, tsum_mul_left, ht.tsum_sub hn,
    tsum_geometric_of_lt_one (le_of_lt h0) h1, negGeom_tsum h0 h1]
  have e1 : (1 : ℝ) - t ≠ 0 := by
    intro hc
    linarith [sub_eq_zero.mp hc]
  have e2 : (1 : ℝ) + t ≠ 0 := by positivity
  have e3 : (1 : ℝ) - t ^ 2 ≠ 0 := by
    have : (1 : ℝ) - t ^ 2 = (1 - t) * (1 + t) := by ring
    rw [this]
    exact mul_ne_zero e1 e2
  field_simp
  ring

/-- **Termwise**: the `b`-th tail term is at least the odd-indicator bound. -/
theorem tail_term_ge {t : ℝ} (h0 : 0 < t) (b : ℕ) :
    -(t ^ 12 * (t ^ b - (-t) ^ b) / 2)
      ≤ (if fibSeq (b + 12) then (-t) ^ (b + 12) else 0) := by
  have hnn : (0 : ℝ) ≤ t ^ b := by positivity
  rcases Nat.even_or_odd b with he | ho
  · have hb : (-t) ^ b = t ^ b := he.neg_pow t
    have hb12 : Even (b + 12) := by
      rcases he with ⟨k, hk⟩
      exact ⟨k + 6, by omega⟩
    rw [hb]
    by_cases hf : fibSeq (b + 12)
    · rw [if_pos hf, hb12.neg_pow]
      have : (0 : ℝ) ≤ t ^ (b + 12) := by positivity
      simp only [sub_self, mul_zero, zero_div, neg_zero]
      exact this
    · rw [if_neg hf]
      simp
  · have hb : (-t) ^ b = -(t ^ b) := ho.neg_pow t
    have hb12 : Odd (b + 12) := by
      rcases ho with ⟨k, hk⟩
      exact ⟨k + 6, by omega⟩
    have hval : -(t ^ 12 * (t ^ b - (-t) ^ b) / 2) = -(t ^ (b + 12)) := by
      rw [hb, pow_add]
      ring
    rw [hval]
    by_cases hf : fibSeq (b + 12)
    · rw [if_pos hf, hb12.neg_pow]
    · rw [if_neg hf]
      have : (0 : ℝ) ≤ t ^ (b + 12) := by positivity
      linarith

theorem tail_ge_twelve {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    -(t ^ 13 / (1 - t ^ 2))
      ≤ ∑' b : ℕ, (if fibSeq (b + 12) then (-t) ^ (b + 12) else 0) := by
  have hg := summable_fibSeq (abs_neg_lt_one h0 h1)
  have hshift : Summable (fun b : ℕ => if fibSeq (b + 12) then (-t) ^ (b + 12) else 0) :=
    (_root_.summable_nat_add_iff
      (f := fun j : ℕ => if fibSeq j then (-t) ^ j else 0) 12).mpr hg
  have hle := (oddPart_summable h0 h1).tsum_le_tsum (fun b => tail_term_ge h0 b) hshift
  rwa [oddPart_tsum h0 h1] at hle

/-- `C_a(-t) = S_12(-t) + (tail from index 12)`. -/
theorem CaFib_split_twelve {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    CaFib (-t) = (1 + t ^ 2 - t ^ 3 - t ^ 5 - t ^ 7 + t ^ 8 + t ^ 10 - t ^ 11)
      + ∑' b : ℕ, (if fibSeq (b + 12) then (-t) ^ (b + 12) else 0) := by
  have hg := summable_fibSeq (abs_neg_lt_one h0 h1)
  rw [CaFib, ← hg.sum_add_tsum_nat_add 12, sum_twelve]

/-- **The band polynomial.**  `(1 - t²)·S_12(t) - t^13 = 1 - t³ - t⁴ + t⁸ + t⁹ - t¹¹ - t¹²`,
and it is positive on `[1/2, 6/7]` — with margin `0.031`, six times what the crude
truncation at `N = 18` would have left. -/
theorem band_poly_pos {t : ℝ} (h1 : 1 / 2 ≤ t) (h2 : t ≤ 6 / 7) :
    0 < 1 - t ^ 3 - t ^ 4 + t ^ 8 + t ^ 9 - t ^ 11 - t ^ 12 := by
  nlinarith [sq_nonneg t, sq_nonneg (t - 1), sq_nonneg (t - 6 / 7), sq_nonneg (t - 1 / 2),
    pow_le_pow_left₀ (by linarith : (0:ℝ) ≤ t) h2 3,
    pow_le_pow_left₀ (by linarith : (0:ℝ) ≤ t) h2 4,
    pow_le_pow_left₀ (by linarith : (0:ℝ) ≤ t) h2 8,
    pow_le_pow_left₀ (by linarith : (0:ℝ) ≤ t) h2 11,
    pow_le_pow_left₀ (by linarith : (0:ℝ) ≤ t) h2 12,
    pow_nonneg (by linarith : (0:ℝ) ≤ t) 8,
    pow_nonneg (by linarith : (0:ℝ) ≤ t) 9]

/-- **THE BAND, CLOSED.**  `C_a(-t) > 0` for `1/2 ≤ t ≤ 6/7`. -/
theorem positive_on_band (t : ℝ) (h1 : 1 / 2 ≤ t) (h2 : t ≤ 6 / 7) : 0 < CaFib (-t) := by
  have h0 : (0 : ℝ) < t := by linarith
  have hlt : t < 1 := by linarith
  have hd : (0 : ℝ) < 1 - t ^ 2 := by nlinarith
  have hsplit := CaFib_split_twelve h0 hlt
  have htail := tail_ge_twelve h0 hlt
  have hpoly := band_poly_pos h1 h2
  have hkey : 0 < (1 + t ^ 2 - t ^ 3 - t ^ 5 - t ^ 7 + t ^ 8 + t ^ 10 - t ^ 11)
      - t ^ 13 / (1 - t ^ 2) := by
    rw [sub_pos, div_lt_iff₀ hd]
    nlinarith [hpoly]
  linarith [hsplit, htail, hkey]

/-- **Conjecture 5.12, on the whole of `(-1,1)`.** -/
theorem positive_of_mem_full {x : ℝ} (hlo : -1 < x) (hhi : x < 1) : 0 < CaFib x := by
  have hx : x = -(-x) := by ring
  by_cases hx0 : 0 ≤ x
  · exact positive_of_nonneg x hx0 hhi
  · rw [not_le] at hx0
    rcases le_or_gt (-x) (1 / 2) with hs | hs
    · rcases eq_or_lt_of_le hs with heq | hlt
      · rw [hx]
        exact positive_on_band (-x) (by linarith) (by linarith)
      · rw [hx]
        exact positive_of_small (-x) (by linarith) hlt
    · rcases le_or_gt (-x) (6 / 7) with hb | hb
      · rw [hx]
        exact positive_on_band (-x) (by linarith) hb
      · rw [hx]
        exact positive_of_six_sevenths (-x) (by linarith) (by linarith)

/-- **CONJECTURE 5.12 OF POUTI–RAMSEY–STRUNGARU**, `arXiv:2309.16100v2`, p. 21: the
`a`-characteristic generating function of the Fibonacci fixed word is strictly positive on
`(-1,1)`.

Nothing is carried.  `C_a` is `CaFib`, DEFINED here, and tied to the source by three
independent anchors: the concatenation recurrence, `subst_fibWord` (`A_{n+1} = σ(A_n)`,
hence `A_n = σⁿ(a)` — the write-up's own sentence) and `fibWord_five` (the printed prefix
`w = abaababa…`).  The write-up's Tasks 2–5 are explicitly "questions for further work, not
additional solved claims", so this is its whole theorem. -/
theorem conjecture_5_12 (x : ℝ) (h : x ∈ Set.Ioo (-1 : ℝ) 1) : 0 < CaFib x :=
  positive_of_mem_full h.1 h.2

end Principia.MathDB.P360139
