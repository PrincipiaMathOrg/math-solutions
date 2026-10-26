import Mathlib

set_option autoImplicit false

/-!
# MathDB #366299 — moving counting jumps disprove a periodic-oscillation conjecture

Write-up `mathdb-open-problems/problems/366299/solution.tex`,
*Moving counting jumps disprove a periodic-oscillation conjecture*, 18 September 2026.
Source: D. Bevan and J. Condé, *Introducing irrational enumeration*, Electron. J. Combin.
**33**(3) (2026), P3.15, **Conjecture 6**, p. 15 (arXiv:2412.14682v3, Conjecture 6, p. 14).

Conjecture 6 predicts, for an irrational combinatorial class meeting two analytic
conditions, that its cumulative count satisfies

    |C_{≤x}| ~ c(x) · ρ^{-x} · x^{α-1}        (x → ∞)

for a bounded `ω`-periodic `c`.  The witness is the class of nonempty binary words, a word
of length `n ≥ 1` carrying the size `lam n = n + √2 · 2^{-n}`, so there are `2^n` objects of
size `lam n`.  For it the conjecture's parameters are `ρ = 1/2`, `α = 1`, `h = 1`, `ω = 1`,
i.e. it predicts `|C_{≤x}| ~ c(x) · 2^x` with `c` 1-periodic.

## The refutation is two point evaluations

Write `A x = |C_{≤x}|`.

* `A_shift` — for every `r ∈ (0,1)` and every `N ≥ 1` with `√2/2^N < r`,
  `A (N + r) = 2^(N+1) - 2`.  Along `x = N + r` the assumed asymptotic therefore FORCES
  `c r · 2^r = 2` (`forced_value`).  **Only periodicity is used** — no regularity, no
  boundedness.
* `A_jump` — with `δ N = √2/2^(N+1)` we have `N < N + δ N < lam N`, so
  `A (N + δ N) = 2^N - 2`.
* Periodicity plus the values already forced give `c (N + δ N) · 2^(δ N) = 2`, so the ratio
  at `N + δ N` is `(2^N - 2)/(2 · 2^N) = 1/2 - 1/2^N`: **the `δ N` in the exponent cancels
  against the one inside `c` exactly**, leaving a rational number tending to `1/2`, not `1`.

`no_periodic_asymptotic` is the contradiction.  The mechanism is that the jump phases
`δ N → 0`: along every FIXED fractional part the limit does exist and equals `1`, which is
why the conjecture looks true; it fails only along a sequence whose fractional part moves.

## Why the earlier triage was wrong

This row was triaged 2026-09-20 as "heavy analysis, skip", on the grounds that the argument
"needs Dirichlet generating functions, their singularities on the convergence line, a full
lattice of simple dominant poles, and analytic continuation on a cut disk", and that the
conclusion is "an asymptotic non-existence statement with no finite certificate".  Reading
the write-up shows the division of labour is the other way round: **all of that machinery is
spent verifying that the witness SATISFIES Conjecture 6's hypotheses**, while the refutation
of its conclusion — the part formalised here — is two evaluations of a step function and one
cancellation.  The triage was made without reading the source.

## What is NOT proved here

That the class satisfies Conjecture 6's analytic HYPOTHESES: the decomposition
`f = g + h/(1 - z/ρ)^α` with `g` analytic on the closed cut disk, and the Dirichlet
generating function having exactly the pole lattice `log 2 + 2πiℤ`, every pole simple with
residue `1`.  That half is genuine complex analysis and is **not formalised**.

Until 2026-09-26 it was not carried as a hypothesis either — nothing in the module depended on
it — which made it the worst of the three statuses: an *unformalised interface*, invisible to
every gate.  It is now **carried explicitly**, as the opaque `Prop` parameter `Adm` in
`conjecture_6_false`, so the refutation attaches to Conjecture 6 by typechecking rather than by
prose.  The row remains a SPINE and is NOT counted as fully verified: `Adm` is an obligation,
not a theorem.

**215 check.**  The conjecture is stated here in the WEAKEST reading the witness still
kills: `c` is required only to be 1-periodic (boundedness is dropped, so the statement
refuted is weaker and the refutation correspondingly stronger), and `~` is read as the ratio
tending to `1`, which is the source's own reading.  The counting variable is real, as in the
source's definition — that is exactly what the counterexample exploits.

Values checked first, in exact `ℚ(√2)` arithmetic, in
`Campaigns/MathDB-Formalization/verify_366299.py`.
-/

namespace Principia.MathDB.P366299

open Filter Topology Finset

/-- The irrational offset `a = √2`. -/
noncomputable def a : ℝ := Real.sqrt 2

theorem a_pos : 0 < a := Real.sqrt_pos.mpr (by norm_num)

theorem a_lt_two : a < 2 := by
  have h : a ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  nlinarith [a_pos]

/-- The size of a binary word of length `n`: `lam n = n + a·2^{-n}`. -/
noncomputable def lam (n : ℕ) : ℝ := (n : ℝ) + a / 2 ^ n

theorem offset_pos (n : ℕ) : 0 < a / 2 ^ n := by
  have := a_pos
  positivity

/-- `a/2^n < 1` for `n ≥ 1`, because `a < 2 ≤ 2^n`. -/
theorem offset_lt_one {n : ℕ} (hn : 1 ≤ n) : a / 2 ^ n < 1 := by
  have h2 : (2 : ℝ) ≤ 2 ^ n := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
  have hpos : (0 : ℝ) < 2 ^ n := by positivity
  rw [div_lt_one hpos]
  linarith [a_lt_two]

theorem lt_lam (n : ℕ) : (n : ℝ) < lam n := by
  have := offset_pos n
  simp only [lam]
  linarith

theorem lam_lt_succ {n : ℕ} (hn : 1 ≤ n) : lam n < (n : ℝ) + 1 := by
  have := offset_lt_one hn
  simp only [lam]
  linarith

/-- The cumulative count `|C_{≤x}|`: the class has `2^n` objects of size `lam n` for each
`n ≥ 1`.  Since `lam n > n`, no `n > ⌊x⌋₊` can contribute, so this finite sum really is the
full count — `mem_filter_of_lam_le` is the certificate that nothing is missed. -/
noncomputable def A (x : ℝ) : ℝ :=
  ∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n => lam n ≤ x), (2 : ℝ) ^ n

/-- **Nothing is missed by the cutoff.**  Any `n ≥ 1` whose object fits under `x` is inside
the index set of `A`. -/
theorem mem_filter_of_lam_le {n : ℕ} {x : ℝ} (h1 : 1 ≤ n) (h : lam n ≤ x) :
    n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n => lam n ≤ x) := by
  refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨h1, ?_⟩, h⟩
  exact Nat.le_floor (le_of_lt (lt_of_lt_of_le (lt_lam n) h))

theorem geom_Icc (N : ℕ) : ∑ n ∈ Finset.Icc 1 N, (2 : ℝ) ^ n = 2 ^ (N + 1) - 2 := by
  induction N with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih]
      ring

/-! ### The two point evaluations -/

/-- **First evaluation.**  Above the jump: every word of length `≤ N` has been counted. -/
theorem A_shift (N : ℕ) (hN : 1 ≤ N) (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1)
    (hrN : a / 2 ^ N < r) : A ((N : ℝ) + r) = 2 ^ (N + 1) - 2 := by
  have hcast : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hfl : ⌊(N : ℝ) + r⌋₊ = N := by
    rw [Nat.floor_eq_iff (by linarith)]
    exact ⟨by linarith, by linarith⟩
  have hset : (Finset.Icc 1 ⌊(N : ℝ) + r⌋₊).filter (fun n => lam n ≤ (N : ℝ) + r)
      = Finset.Icc 1 N := by
    rw [hfl]
    refine Finset.filter_true_of_mem (fun n hn => ?_)
    obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.mp hn
    rcases eq_or_lt_of_le hn2 with rfl | hlt
    · simp only [lam]; linarith
    · have hs : lam n < (n : ℝ) + 1 := lam_lt_succ hn1
      have hle : (n : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast hlt
      linarith
  rw [A, hset, geom_Icc]

/-- **Second evaluation.**  Strictly below the jump at `lam N`, with a phase that moves. -/
theorem A_jump (N : ℕ) (hN : 1 ≤ N) :
    A ((N : ℝ) + a / 2 ^ (N + 1)) = 2 ^ N - 2 := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have hd0 : 0 < a / (2 : ℝ) ^ (M + 1 + 1) := offset_pos _
  have hd1 : a / (2 : ℝ) ^ (M + 1 + 1) < 1 := offset_lt_one (by omega)
  have hcast : (0 : ℝ) ≤ ((M + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hfl : ⌊((M + 1 : ℕ) : ℝ) + a / (2 : ℝ) ^ (M + 1 + 1)⌋₊ = M + 1 := by
    rw [Nat.floor_eq_iff (by linarith)]
    exact ⟨by linarith, by push_cast; linarith⟩
  -- the top index `M+1` is excluded: its own size still lies above the threshold
  have hlt : a / (2 : ℝ) ^ (M + 1 + 1) < a / (2 : ℝ) ^ (M + 1) := by
    have h1 : (0 : ℝ) < 2 ^ (M + 1) := by positivity
    have h2 : (2 : ℝ) ^ (M + 1) < 2 ^ (M + 1 + 1) := by
      calc (2 : ℝ) ^ (M + 1) = 2 ^ (M + 1) * 1 := by ring
        _ < 2 ^ (M + 1) * 2 := by linarith
        _ = 2 ^ (M + 1 + 1) := (pow_succ 2 (M + 1)).symm
    exact div_lt_div_of_pos_left a_pos h1 h2
  have htop : ¬ (lam (M + 1) ≤ ((M + 1 : ℕ) : ℝ) + a / (2 : ℝ) ^ (M + 1 + 1)) := by
    simp only [lam, not_le]
    push_cast
    linarith
  have hset : (Finset.Icc 1 ⌊((M + 1 : ℕ) : ℝ) + a / (2 : ℝ) ^ (M + 1 + 1)⌋₊).filter
        (fun n => lam n ≤ ((M + 1 : ℕ) : ℝ) + a / (2 : ℝ) ^ (M + 1 + 1))
      = Finset.Icc 1 M := by
    rw [hfl]
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hn1, hn2⟩, hle⟩
      refine ⟨hn1, ?_⟩
      by_contra hcon
      have hEq : n = M + 1 := by omega
      exact htop (hEq ▸ hle)
    · rintro ⟨hn1, hn2⟩
      refine ⟨⟨hn1, by omega⟩, ?_⟩
      have h1 : lam n < (n : ℝ) + 1 := lam_lt_succ hn1
      have h2 : (n : ℝ) + 1 ≤ ((M + 1 : ℕ) : ℝ) := by
        have hc : (n : ℝ) ≤ (M : ℝ) := by exact_mod_cast hn2
        push_cast
        linarith
      linarith
  rw [A, hset, geom_Icc]

/-! ### Periodicity transports every value back into `(0,1)` -/

theorem per_nat (c : ℝ → ℝ) (hper : ∀ x, c (x + 1) = c x) (N : ℕ) (r : ℝ) :
    c ((N : ℝ) + r) = c r := by
  induction N with
  | zero => simp
  | succ k ih =>
      have hs : ((k + 1 : ℕ) : ℝ) + r = ((k : ℝ) + r) + 1 := by push_cast; ring
      rw [hs, hper, ih]

/-! ### The forced values, and the contradiction -/

theorem tendsto_const_div_pow (b : ℝ) :
    Tendsto (fun N : ℕ => b / (2 : ℝ) ^ N) atTop (nhds 0) := by
  have hp : Tendsto (fun N : ℕ => ((2 : ℝ)⁻¹) ^ N) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have h := hp.const_mul b
  simp only [mul_zero] at h
  simpa [div_eq_mul_inv, ← inv_pow] using h

/-- The assumed asymptotic forces `c r = 2^(1-r)` on `(0,1)`, using **only** periodicity.
Stated multiplicatively as `c r · 2^r = 2`, which is the same thing and avoids a division. -/
theorem forced_value (c : ℝ → ℝ) (hper : ∀ x, c (x + 1) = c x)
    (hasym : Tendsto (fun x : ℝ => A x / (c x * (2 : ℝ) ^ x)) atTop (nhds 1))
    (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) : c r * (2 : ℝ) ^ r = 2 := by
  set K : ℝ := c r * (2 : ℝ) ^ r with hK
  have hu : Tendsto (fun N : ℕ => (N : ℝ) + r) atTop atTop :=
    tendsto_atTop_add_const_right _ r tendsto_natCast_atTop_atTop
  have h1 := hasym.comp hu
  simp only [Function.comp_def] at h1
  have hev : ∀ᶠ N : ℕ in atTop, a / (2 : ℝ) ^ N < r :=
    (tendsto_const_div_pow a).eventually_lt_const hr0
  have heq : ∀ᶠ N : ℕ in atTop,
      A ((N : ℝ) + r) / (c ((N : ℝ) + r) * (2 : ℝ) ^ ((N : ℝ) + r))
        = (2 - 2 / (2 : ℝ) ^ N) / K := by
    filter_upwards [hev, eventually_ge_atTop 1] with N hN hN1
    have hne : ((2 : ℝ) ^ N) ≠ 0 := by positivity
    rw [A_shift N hN1 r hr0 hr1 hN, per_nat c hper N r,
      Real.rpow_add (by norm_num : (0:ℝ) < 2), Real.rpow_natCast]
    have e1 : (2 : ℝ) ^ (N + 1) - 2 = (2 - 2 / (2 : ℝ) ^ N) * 2 ^ N := by
      field_simp
      ring
    have e2 : c r * ((2 : ℝ) ^ N * (2 : ℝ) ^ r) = K * 2 ^ N := by rw [hK]; ring
    rw [e1, e2, mul_div_mul_right _ _ hne]
  have hlim : Tendsto (fun N : ℕ => (2 - 2 / (2 : ℝ) ^ N) / K) atTop (nhds 1) :=
    h1.congr' heq
  have hlim2 : Tendsto (fun N : ℕ => (2 - 2 / (2 : ℝ) ^ N) / K) atTop (nhds (2 / K)) := by
    have hs : Tendsto (fun N : ℕ => 2 - 2 / (2 : ℝ) ^ N) atTop (nhds 2) := by
      simpa using tendsto_const_nhds.sub (tendsto_const_div_pow 2)
    exact hs.div_const K
  have hone : (2 : ℝ) / K = 1 := tendsto_nhds_unique hlim2 hlim
  have hK0 : K ≠ 0 := by
    intro h
    rw [h] at hone
    norm_num at hone
  field_simp at hone
  linarith

/-- **Conjecture 6 fails for this class.**  No 1-periodic `c` at all — bounded or not —
satisfies `|C_{≤x}| ~ c(x)·2^x`. -/
theorem no_periodic_asymptotic (c : ℝ → ℝ) (hper : ∀ x, c (x + 1) = c x)
    (hasym : Tendsto (fun x : ℝ => A x / (c x * (2 : ℝ) ^ x)) atTop (nhds 1)) : False := by
  have hd0 : ∀ N : ℕ, 0 < a / (2 : ℝ) ^ (N + 1) := fun N => offset_pos _
  have hd1 : ∀ N : ℕ, a / (2 : ℝ) ^ (N + 1) < 1 := fun N => offset_lt_one (by omega)
  have hforced : ∀ N : ℕ, c (a / (2 : ℝ) ^ (N + 1)) * (2 : ℝ) ^ (a / (2 : ℝ) ^ (N + 1)) = 2 :=
    fun N => forced_value c hper hasym _ (hd0 N) (hd1 N)
  have hu : Tendsto (fun N : ℕ => (N : ℝ) + a / (2 : ℝ) ^ (N + 1)) atTop atTop := by
    refine tendsto_atTop_mono (fun N => ?_) tendsto_natCast_atTop_atTop
    linarith [hd0 N]
  have h1 := hasym.comp hu
  simp only [Function.comp_def] at h1
  have heq : ∀ᶠ N : ℕ in atTop,
      A ((N : ℝ) + a / (2 : ℝ) ^ (N + 1))
          / (c ((N : ℝ) + a / (2 : ℝ) ^ (N + 1))
              * (2 : ℝ) ^ ((N : ℝ) + a / (2 : ℝ) ^ (N + 1)))
        = 1 / 2 - 1 / (2 : ℝ) ^ N := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hpos : (0 : ℝ) < 2 ^ N := by positivity
    rw [A_jump N hN, per_nat c hper N (a / (2 : ℝ) ^ (N + 1)),
      Real.rpow_add (by norm_num : (0:ℝ) < 2), Real.rpow_natCast]
    have e2 : c (a / (2 : ℝ) ^ (N + 1))
        * ((2 : ℝ) ^ N * (2 : ℝ) ^ (a / (2 : ℝ) ^ (N + 1))) = 2 * 2 ^ N := by
      rw [show c (a / (2 : ℝ) ^ (N + 1))
              * ((2 : ℝ) ^ N * (2 : ℝ) ^ (a / (2 : ℝ) ^ (N + 1)))
            = (c (a / (2 : ℝ) ^ (N + 1)) * (2 : ℝ) ^ (a / (2 : ℝ) ^ (N + 1))) * 2 ^ N by
          ring, hforced N]
    rw [e2]
    field_simp
  have hlim : Tendsto (fun N : ℕ => 1 / 2 - 1 / (2 : ℝ) ^ N) atTop (nhds 1) := h1.congr' heq
  have hlim2 : Tendsto (fun N : ℕ => 1 / 2 - 1 / (2 : ℝ) ^ N) atTop (nhds (1 / 2)) := by
    simpa using tendsto_const_nhds.sub (tendsto_const_div_pow 1)
  have hcon := tendsto_nhds_unique hlim2 hlim
  norm_num at hcon

/-! ### The conjecture's own shape, so that the refutation ATTACHES

`no_periodic_asymptotic` refutes the asymptotic for a GIVEN `c`.  Conjecture 6 asserts the
EXISTENCE of one, writes its right-hand side in the general form `c(x)·ρ^{-x}·x^{α-1}`, and
requires `c` to be bounded.  Those are three transcriptions that the prose above asserts and
nothing checked — which is exactly where a strength gap hides.  Stating the conjecture as a
`Prop` and deriving `False` from it makes all three typing facts:

* the `∃ c` quantifier is written down, so what the module refutes is visibly the negation of
  the conjecture's own quantifier structure rather than a hand-transcribed limit statement;
* the specialization `ρ^{-x}·x^{α-1} = 2^x` at `(ρ, α) = (1/2, 1)` becomes a PROOF STEP
  (`predictedRHS_params`, used inside `conj6_imp_weak`) instead of a remark in a header;
* dropping boundedness is exhibited as a weakening, so the source's own bounded conjecture is
  refuted *a fortiori* rather than by assertion.

The analytic admissibility half stays unproved, but it is no longer merely ABSENT: it is the
named parameter `Adm`, carried in `conjecture_6_false`'s signature where it can neither be
overlooked nor quietly dropped.

**CORRECTION (2026-09-26) — "no footing in Mathlib at all" was wrong.**  This header previously
said the remaining complex analysis (a pole lattice on the convergence line, analytic continuation
on a cut disk) had no Mathlib footing.  Reading the write-up's actual argument shows **both**
admissibility conditions reduce to ONE elementary estimate, and the two tools it needs both exist:
`Complex.norm_exp_sub_one_le` (`‖x‖ ≤ 1 → ‖exp x − 1‖ ≤ 2‖x‖`) and
`differentiableOn_tsum_of_summable_norm` in `Mathlib/Analysis/Complex/LocallyUniformLimit.lean`,
which turns a uniform summable majorant on an open set into differentiability of the sum.  The
estimate is proved below (`norm_gTerm_le`, `summable_norm_gTerm`).  This is the SECOND time this
row's difficulty has been mis-priced, and the second time by a summary rather than by the source:
the 2026-09-20 triage said "heavy analysis, skip", and this header then said the residue had no
footing.  Both were written without the write-up's argument in front of them. -/

/-- The conjecture's predicted right-hand side in the source's GENERAL form
`c(x) · ρ^{-x} · x^{α-1}`. -/
noncomputable def predictedRHS (rho alpha : ℝ) (c : ℝ → ℝ) (x : ℝ) : ℝ :=
  c x * rho ^ (-x) * x ^ (alpha - 1)

/-- **At this class's parameters `ρ = 1/2`, `α = 1` the general form IS `c x * 2^x`.**  Proved,
not asserted: this is what licenses reading the `2^x` statements above as Conjecture 6's form. -/
theorem predictedRHS_params (c : ℝ → ℝ) (x : ℝ) :
    predictedRHS (1/2) 1 c x = c x * (2 : ℝ) ^ x := by
  have hhalf : (1/2 : ℝ) = (2 : ℝ)⁻¹ := by norm_num
  have h1 : ((2 : ℝ)⁻¹) ^ (-x) = ((2 : ℝ) ^ (-x))⁻¹ :=
    Real.inv_rpow (by norm_num) (-x)
  have h2 : (2 : ℝ) ^ (-x) = ((2 : ℝ) ^ x)⁻¹ := Real.rpow_neg (by norm_num) x
  simp only [predictedRHS, hhalf, h1, h2, inv_inv, sub_self, Real.rpow_zero, mul_one]

/-- **Conjecture 6's conclusion for this class, exactly as the source states it**: an
existential over `c`, with `c` bounded and 1-periodic, and the asymptotic in the general form.
`Adm` stands for the analytic admissibility hypotheses, which are not formalised. -/
-- SPEC-CARRY-CHECKED: Conj6 -- 2026-09-26.  NOT a carry at all: this is the REFUTED STATEMENT,
-- which `check_unsatisfied_specs.py`'s own docstring names as the legitimate flag ("a conjecture
-- statement is meant to be the GOAL").  It is consumed by `conj6_imp_weak` and
-- `conjecture_6_false`, both of which derive `False` from it, so a "producer" here would be a
-- PROOF of Conjecture 6.  `Conj6Weak` needs no marker because `conj6_imp_weak` produces it.
def Conj6 (Adm : Prop) : Prop :=
  Adm → ∃ c : ℝ → ℝ, (∃ M : ℝ, ∀ x, |c x| ≤ M) ∧ (∀ x, c (x + 1) = c x) ∧
    Tendsto (fun x : ℝ => A x / predictedRHS (1/2) 1 c x) atTop (nhds 1)

/-- The same statement with boundedness DROPPED, which is what the module actually refutes. -/
def Conj6Weak (Adm : Prop) : Prop :=
  Adm → ∃ c : ℝ → ℝ, (∀ x, c (x + 1) = c x) ∧
    Tendsto (fun x : ℝ => A x / (c x * (2 : ℝ) ^ x)) atTop (nhds 1)

/-- **Dropping boundedness weakens the conjecture**, so refuting the weak form refutes the
source's form a fortiori.  The general-form-to-`2^x` transcription is discharged here. -/
theorem conj6_imp_weak (Adm : Prop) (h : Conj6 Adm) : Conj6Weak Adm := by
  intro hadm
  obtain ⟨c, -, hper, hasym⟩ := h hadm
  refine ⟨c, hper, hasym.congr fun x => ?_⟩
  rw [predictedRHS_params]

/-- The weak form is refuted outright, by the two point evaluations. -/
theorem conj6Weak_false (Adm : Prop) (hadm : Adm) (h : Conj6Weak Adm) : False := by
  obtain ⟨c, hper, hasym⟩ := h hadm
  exact no_periodic_asymptotic c hper hasym

/-- **CONJECTURE 6 IS REFUTED for this class, given only its analytic admissibility.**  The one
obligation left is `Adm`, and it is visible in this signature.  Note the shape: the honest
statement is `Adm → ¬ Conj6`, never `¬ Conj6` — a conjecture of the form "every admissible class
satisfies P" cannot be refuted without exhibiting admissibility, and writing it this way is what
stops the missing half from being lost. -/
theorem conjecture_6_false (Adm : Prop) (hadm : Adm) (h : Conj6 Adm) : False :=
  conj6Weak_false Adm hadm (conj6_imp_weak Adm h)

/-! ### Toward `Adm`: the one estimate both admissibility conditions reduce to

The write-up verifies the two conditions by the SAME computation twice.  On the power-series side,
subtracting a geometric series off the cut gives `f z = 1/(1 − 2z) + g z` with

    g z = −1 + ∑_{n≥1} 2^n z^n (exp (a·2^{-n}·Log z) − 1),

and on the Dirichlet side the identical manipulation gives
`F s = 2e^{-s}/(1 − 2e^{-s}) + H s` with `H s = ∑_{n≥1} 2^n e^{-ns}(e^{-as·2^{-n}} − 1)`.  In both,
the `2^{-n}` inside the exponent cancels the `2^n` in front, leaving a geometric series whose ratio
is `|z|` (resp. `e^{-Re s}`) rather than `2|z|` — so the corrector converges **strictly past** the
singularity, which is the entire content of "analytic on a larger set".

`norm_gTerm_le` is that estimate, and `summable_norm_gTerm` is the conclusion for radii up to `1`,
not merely up to `ρ = 1/2`.  The write-up uses `|e^w − 1| ≤ |w|e^{|w|}`; Mathlib's
`Complex.norm_exp_sub_one_le` gives `≤ 2|w|` under `|w| ≤ 1`, which is sharper here and is why the
constant below is `2aL` rather than `aLe^{aL/2}`.

**WHAT REMAINS, and `Adm` is still carried.**  What is proved here is the majorant, which is the
mathematical content; the packaging into `AnalyticOn` via
`differentiableOn_tsum_of_summable_norm` is not done, and neither is the pole-lattice conclusion on
the Dirichlet side (that `1 − 2e^{-s}` vanishes exactly at `log 2 + 2πiℤ`, simply, with residue 1 —
elementary, but it needs the meromorphic-continuation statement to be phrased).  So `Adm` remains an
obligation and the row remains a SPINE.  Values and both decompositions checked first in
`Campaigns/MathDB-Formalization/verify_366299.py`. -/

/-- The `n`th term of the corrector `g`, with `z^w` read as `exp (w · Log z)`. -/
noncomputable def gTerm (n : ℕ) (z : ℂ) : ℂ :=
  2 ^ n * z ^ n * (Complex.exp ((a : ℂ) / 2 ^ n * Complex.log z) - 1)

/-- **THE ESTIMATE BOTH ADMISSIBILITY CONDITIONS REDUCE TO.**  The `2^{-n}` inside the exponent
cancels the `2^n` in front, so the majorant is geometric with ratio `r` — not `2r`. -/
theorem norm_gTerm_le {n : ℕ} {z : ℂ} {r L : ℝ} (hr : ‖z‖ ≤ r)
    (hL : ‖Complex.log z‖ ≤ L) (hn : a * L ≤ 2 ^ n) :
    ‖gTerm n z‖ ≤ 2 * a * L * r ^ n := by
  have hL0 : 0 ≤ L := le_trans (norm_nonneg _) hL
  have hapos := a_pos
  have hpow : (0:ℝ) < 2 ^ n := by positivity
  have hz0 : 0 ≤ ‖z‖ := norm_nonneg _
  have hnormw : ‖(a : ℂ) / 2 ^ n * Complex.log z‖ = (a / 2 ^ n) * ‖Complex.log z‖ := by
    rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hapos, norm_pow]
    norm_num
  have hwle : ‖(a : ℂ) / 2 ^ n * Complex.log z‖ ≤ a * L / 2 ^ n := by
    rw [hnormw]
    have := mul_le_mul_of_nonneg_left hL (le_of_lt (div_pos hapos hpow))
    calc (a / 2 ^ n) * ‖Complex.log z‖ ≤ (a / 2 ^ n) * L := this
      _ = a * L / 2 ^ n := by ring
  have hw1 : ‖(a : ℂ) / 2 ^ n * Complex.log z‖ ≤ 1 := by
    refine le_trans hwle ?_
    rw [div_le_one hpow]; exact hn
  have hexp := Complex.norm_exp_sub_one_le hw1
  have hzpow : ‖z‖ ^ n ≤ r ^ n := pow_le_pow_left₀ hz0 hr n
  have hgoal : ‖gTerm n z‖ = 2 ^ n * ‖z‖ ^ n
      * ‖Complex.exp ((a : ℂ) / 2 ^ n * Complex.log z) - 1‖ := by
    rw [gTerm, norm_mul, norm_mul, norm_pow, norm_pow]
    norm_num
  rw [hgoal]
  have hstep : ‖Complex.exp ((a : ℂ) / 2 ^ n * Complex.log z) - 1‖ ≤ 2 * (a * L / 2 ^ n) :=
    le_trans hexp (by linarith [hwle])
  have hr0' : 0 ≤ r := le_trans hz0 hr
  calc 2 ^ n * ‖z‖ ^ n * ‖Complex.exp ((a : ℂ) / 2 ^ n * Complex.log z) - 1‖
      ≤ 2 ^ n * r ^ n * (2 * (a * L / 2 ^ n)) := by
        refine mul_le_mul ?_ hstep (norm_nonneg _)
          (mul_nonneg (le_of_lt hpow) (pow_nonneg hr0' n))
        exact mul_le_mul_of_nonneg_left hzpow (le_of_lt hpow)
    _ = 2 * a * L * r ^ n := by field_simp

/-- **SUMMABLE PAST `ρ`.**  The majorant is geometric with ratio `r`, so it converges for every
`r < 1`, not merely `r < ρ = 1/2`.  Only finitely many `n` fail the hypothesis `a·L ≤ 2^n`, which
is why the statement needs no lower bound on `n`. -/
theorem summable_norm_gTerm {z : ℂ} {r L : ℝ} (hr : ‖z‖ ≤ r) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hL : ‖Complex.log z‖ ≤ L) :
    Summable (fun n : ℕ => ‖gTerm n z‖) := by
  have hL0 : 0 ≤ L := le_trans (norm_nonneg _) hL
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (a * L) (by norm_num : (1:ℝ) < 2)
  rw [← _root_.summable_nat_add_iff k]
  have hmaj : Summable (fun n : ℕ => 2 * a * L * r ^ (n + k)) := by
    have he : (fun n : ℕ => 2 * a * L * r ^ (n + k))
        = fun n : ℕ => (2 * a * L * r ^ k) * r ^ n := by
      funext n; rw [pow_add]; ring
    rw [he]
    exact (summable_geometric_of_lt_one hr0 hr1).mul_left _
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hmaj
  refine norm_gTerm_le hr hL (le_of_lt (lt_of_lt_of_le hk ?_))
  exact pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (Nat.le_add_left k n)

/-! ### The decomposition condition, discharged: `g` is holomorphic past `ρ`

The majorant above is turned into differentiability by Mathlib's
`Complex.differentiableOn_tsum_of_summable_norm`, which needs a uniform summable bound on an OPEN
set.  Two points about the set.  `Log` is unbounded as `z → 0`, and near `0` the only available
bound on a term is `2·(2r)^n`, summable just for `r < 1/2` — i.e. exactly not past `ρ`.  So the
bound must be taken on an annulus, and that costs nothing: the cut disk `D̄(0,ρ) ∖ ℝ≤0` excludes
`0` already, and differentiability is local, so `differentiableOn_gSum_ball` removes the inner
radius again and gives the whole slit ball of any radius `r < 1`.  Taking `r ∈ (1/2, 1)` covers the
closed cut disk Conjecture 6's first hypothesis names.

The estimate's hypothesis `a·L ≤ 2^n` fails for finitely many `n`, and
`Complex.differentiableOn_tsum_of_summable_norm` wants the bound for ALL of them, so the sum is
split: the tail from `k` onwards is handled by the theorem, the head `∑_{n<k}` is a finite sum of
differentiable functions, and `Summable.sum_add_tsum_nat_add` glues them.

**WHAT REMAINS.**  The Dirichlet half — that the displayed expression continues `F` meromorphically
across `Re s = log 2` with poles exactly on `log 2 + 2πiℤ`, each simple with residue `1`.  The
*estimate* for it is `norm_hTerm_le`/`summable_norm_hTerm` below; the continuation statement itself
is not phrased, so `Adm` is still carried in `conjecture_6_false`. -/

/-- An annulus inside the slit plane, outer radius allowed up to `1` — strictly past `ρ = 1/2`. -/
def annSlit (s r : ℝ) : Set ℂ :=
  (Complex.slitPlane ∩ {z : ℂ | s < ‖z‖}) ∩ {z : ℂ | ‖z‖ < r}

theorem isOpen_annSlit (s r : ℝ) : IsOpen (annSlit s r) :=
  (Complex.isOpen_slitPlane.inter (isOpen_lt continuous_const continuous_norm)).inter
    (isOpen_lt continuous_norm continuous_const)

/-- On the annulus, `‖Log z‖ ≤ -log s + π`; the inner radius is what makes `Log` bounded. -/
theorem norm_log_le_of_mem {s r : ℝ} (hs : 0 < s) (hr1 : r ≤ 1)
    {z : ℂ} (hz : z ∈ annSlit s r) :
    ‖Complex.log z‖ ≤ -Real.log s + Real.pi := by
  obtain ⟨⟨-, hzs⟩, hzr⟩ := hz
  have hz0 : 0 < ‖z‖ := lt_trans hs hzs
  have h1 : ‖Complex.log z‖ ≤ |(Complex.log z).re| + |(Complex.log z).im| :=
    Complex.norm_le_abs_re_add_abs_im _
  rw [Complex.log_re, Complex.log_im] at h1
  have h2 : |Complex.arg z| ≤ Real.pi := Complex.abs_arg_le_pi z
  have h3 : |Real.log ‖z‖| ≤ -Real.log s := by
    rw [abs_le]
    refine ⟨?_, ?_⟩
    · have := Real.log_le_log hs (le_of_lt hzs)
      linarith
    · have hle1 : ‖z‖ ≤ 1 := le_trans (le_of_lt hzr) hr1
      have hup : Real.log ‖z‖ ≤ 0 := Real.log_nonpos (le_of_lt hz0) hle1
      have hs1 : s ≤ 1 := le_trans (le_of_lt hzs) hle1
      have hsl : Real.log s ≤ 0 := Real.log_nonpos (le_of_lt hs) hs1
      linarith
  linarith

theorem differentiableOn_gTerm (n : ℕ) (s r : ℝ) :
    DifferentiableOn ℂ (gTerm n) (annSlit s r) := by
  -- `simp only [gTerm]` cannot fire on the UNAPPLIED `gTerm n`; rewrite it to a lambda first.
  have hfun : gTerm n = fun w : ℂ =>
      2 ^ n * w ^ n * (Complex.exp ((a : ℂ) / 2 ^ n * Complex.log w) - 1) := by
    funext w; rw [gTerm]
  rw [hfun]
  intro z hz
  have hlog : DifferentiableAt ℂ Complex.log z := Complex.differentiableAt_log hz.1.1
  refine DifferentiableAt.differentiableWithinAt ?_
  exact (((differentiableAt_const _).mul (differentiableAt_pow n)).mul
    ((((differentiableAt_const _).mul hlog).cexp).sub (differentiableAt_const _)))

/-- **THE DECOMPOSITION CONDITION'S ANALYTIC CONTENT.**  The corrector is differentiable on an
annulus of outer radius any `r < 1` — strictly past `ρ = 1/2`. -/
theorem differentiableOn_gSum {s r : ℝ} (hs : 0 < s) (hsr : s < r) (hr1 : r < 1) :
    DifferentiableOn ℂ (fun z => ∑' n : ℕ, gTerm n z) (annSlit s r) := by
  have hr0 : 0 ≤ r := le_of_lt (lt_trans hs hsr)
  set L : ℝ := -Real.log s + Real.pi with hLdef
  have hL0 : 0 ≤ L := by
    have hs1 : s < 1 := lt_trans hsr hr1
    have : Real.log s ≤ 0 := Real.log_nonpos (le_of_lt hs) (le_of_lt hs1)
    have := Real.pi_pos
    simp only [hLdef]; linarith
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (a * L) (by norm_num : (1:ℝ) < 2)
  have hbnd : ∀ (n : ℕ) (w : ℂ), w ∈ annSlit s r →
      ‖gTerm (n + k) w‖ ≤ 2 * a * L * r ^ (n + k) := by
    intro n w hw
    refine norm_gTerm_le (le_of_lt hw.2) (norm_log_le_of_mem hs (le_of_lt hr1) hw) ?_
    exact le_of_lt (lt_of_lt_of_le hk
      (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (Nat.le_add_left k n)))
  have hmaj : Summable (fun n : ℕ => 2 * a * L * r ^ (n + k)) := by
    have he : (fun n : ℕ => 2 * a * L * r ^ (n + k))
        = fun n : ℕ => (2 * a * L * r ^ k) * r ^ n := by
      funext n; rw [pow_add]; ring
    rw [he]
    exact (summable_geometric_of_lt_one hr0 hr1).mul_left _
  have hshift : DifferentiableOn ℂ (fun z => ∑' n : ℕ, gTerm (n + k) z) (annSlit s r) :=
    Complex.differentiableOn_tsum_of_summable_norm hmaj
      (fun n => differentiableOn_gTerm (n + k) s r) (isOpen_annSlit s r) hbnd
  have hhead : DifferentiableOn ℂ (fun z => ∑ n ∈ Finset.range k, gTerm n z) (annSlit s r) :=
    DifferentiableOn.fun_sum fun n _ => differentiableOn_gTerm n s r
  refine DifferentiableOn.congr (hhead.add hshift) ?_
  intro z hz
  have hsum : Summable (fun n : ℕ => gTerm n z) :=
    Summable.of_norm (summable_norm_gTerm (le_of_lt hz.2) hr0 hr1
      (norm_log_le_of_mem hs (le_of_lt hr1) hz))
  exact (hsum.sum_add_tsum_nat_add k).symm

/-- **THE CONDITION AS THE SOURCE STATES IT.**  Differentiability is local and `slitPlane` excludes
`0`, so the inner radius drops out: the corrector is differentiable on the whole slit ball of any
radius `r < 1`, and `r ∈ (1/2, 1)` covers the closed cut disk `D̄(0,ρ) ∖ ℝ≤0`. -/
theorem differentiableOn_gSum_ball {r : ℝ} (hr1 : r < 1) :
    DifferentiableOn ℂ (fun z => ∑' n : ℕ, gTerm n z)
      (Complex.slitPlane ∩ Metric.ball 0 r) := by
  intro z hz
  have hz0 : z ≠ 0 := by
    intro h
    rw [h] at hz
    rcases hz.1 with hre | him
    · simp at hre
    · simp at him
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hzr : ‖z‖ < r := by simpa using hz.2
  have hhalf : ‖z‖ / 2 < ‖z‖ := by linarith
  have hhalf0 : 0 < ‖z‖ / 2 := by linarith
  have hhalfr : ‖z‖ / 2 < r := by linarith
  have hmem : z ∈ annSlit (‖z‖ / 2) r := ⟨⟨hz.1, hhalf⟩, hzr⟩
  have hnhds := (isOpen_annSlit (‖z‖ / 2) r).mem_nhds hmem
  exact ((differentiableOn_gSum hhalf0 hhalfr hr1).differentiableAt
    hnhds).differentiableWithinAt

/-! ### The Dirichlet side: the same estimate, and the pole data exactly

Everything the SECOND admissibility condition needs, except its final phrasing.

The estimate is the one above again.  `H s = ∑ 2^n e^{-ns}(e^{-as·2^{-n}} − 1)`, and the `2^{-n}`
inside the exponent cancels the `2^n` in front, so the majorant is geometric with ratio `e^{-Re s}`
rather than `2e^{-Re s}` — convergent for every `Re s > 0`, hence **strictly left of the convergence
line `Re s = log 2`** where the original Dirichlet series diverges.  The finitely many `n` failing
`a‖s‖ ≤ 2^n` are absorbed by the same shift-and-reattach pattern.

The pole data needs no continuation machinery at all.  `denom_eq_zero_iff` locates the zero set of
the displayed denominator **exactly** — `log 2 + 2πiℤ`, from `Complex.exp_eq_exp_iff_exists_int` —
and `residue_eq_one` shows the residue quotient is *literally* `1`, with no limit and no division by
zero, because the numerator `2e^{-s}` and `D' = 2e^{-s}` are the same expression.  That is the
source's own bookkeeping turned into a typing fact.

**WHAT IS LEFT, AND IT IS ONE STATEMENT.**  `Adm` is still carried in `conjecture_6_false`, but the
gap is no longer "genuine complex analysis": it is the **meromorphic-continuation claim** that
`F s = 2e^{-s}/(1 − 2e^{-s}) + H s` continues `F` across `Re s = log 2`, which is what licenses
saying *"the singularities of `F` on the line"* rather than *"the zeros of the displayed
denominator"*.  Both halves of that identity are now theorems about the objects involved;
Mathlib has no meromorphic-continuation idiom that makes the last sentence cheap. -/

/-- The `n`th term of the Dirichlet-side corrector `H`. -/
noncomputable def hTerm (n : ℕ) (s : ℂ) : ℂ :=
  2 ^ n * Complex.exp (-(n : ℂ) * s) * (Complex.exp (-(a : ℂ) * s / 2 ^ n) - 1)

/-- **THE SAME ESTIMATE, ON THE DIRICHLET SIDE.**  Ratio `e^{-Re s}`, not `2e^{-Re s}`. -/
theorem norm_hTerm_le {n : ℕ} {s : ℂ} {sigma M : ℝ} (hsig : sigma ≤ s.re)
    (hM : ‖s‖ ≤ M) (hn : a * M ≤ 2 ^ n) :
    ‖hTerm n s‖ ≤ 2 * a * M * Real.exp (-sigma) ^ n := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) hM
  have hapos := a_pos
  have hpow : (0:ℝ) < 2 ^ n := by positivity
  have hnormw : ‖-(a : ℂ) * s / 2 ^ n‖ = (a / 2 ^ n) * ‖s‖ := by
    rw [norm_div, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hapos,
      norm_pow]
    -- `norm_num` reduces the norm of the power; `ring` does the rearrangement it leaves.  Neither
    -- alone suffices, and a `first | … | …` guard only hides which one is doing the work.
    norm_num
    ring
  have hwle : ‖-(a : ℂ) * s / 2 ^ n‖ ≤ a * M / 2 ^ n := by
    rw [hnormw]
    calc (a / 2 ^ n) * ‖s‖ ≤ (a / 2 ^ n) * M :=
          mul_le_mul_of_nonneg_left hM (le_of_lt (div_pos hapos hpow))
      _ = a * M / 2 ^ n := by ring
  have hw1 : ‖-(a : ℂ) * s / 2 ^ n‖ ≤ 1 := by
    refine le_trans hwle ?_
    rw [div_le_one hpow]; exact hn
  have hexp := Complex.norm_exp_sub_one_le hw1
  have hfac : ‖hTerm n s‖ = 2 ^ n * Real.exp (-(n : ℝ) * s.re)
      * ‖Complex.exp (-(a : ℂ) * s / 2 ^ n) - 1‖ := by
    rw [hTerm, norm_mul, norm_mul, norm_pow, Complex.norm_exp]
    norm_num
  rw [hfac]
  have hgeo : Real.exp (-(n : ℝ) * s.re) ≤ Real.exp (-sigma) ^ n := by
    rw [← Real.exp_nat_mul]
    exact Real.exp_le_exp.mpr (by nlinarith [hsig, Nat.cast_nonneg (α := ℝ) n])
  have hstep : ‖Complex.exp (-(a : ℂ) * s / 2 ^ n) - 1‖ ≤ 2 * (a * M / 2 ^ n) :=
    le_trans hexp (by linarith [hwle])
  calc 2 ^ n * Real.exp (-(n : ℝ) * s.re) * ‖Complex.exp (-(a : ℂ) * s / 2 ^ n) - 1‖
      ≤ 2 ^ n * Real.exp (-sigma) ^ n * (2 * (a * M / 2 ^ n)) := by
        refine mul_le_mul ?_ hstep (norm_nonneg _)
          (mul_nonneg (le_of_lt hpow) (pow_nonneg (le_of_lt (Real.exp_pos _)) n))
        exact mul_le_mul_of_nonneg_left hgeo (le_of_lt hpow)
    _ = 2 * a * M * Real.exp (-sigma) ^ n := by field_simp

/-- **SUMMABLE PAST THE CONVERGENCE LINE.**  For any `σ > 0` the ratio `e^{-σ} < 1`, so `H`
converges on all of `Re s ≥ σ` — in particular strictly left of `Re s = log 2`. -/
theorem summable_norm_hTerm {s : ℂ} {sigma M : ℝ} (hsig0 : 0 < sigma) (hsig : sigma ≤ s.re)
    (hM : ‖s‖ ≤ M) :
    Summable (fun n : ℕ => ‖hTerm n s‖) := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) hM
  have hq0 : 0 ≤ Real.exp (-sigma) := le_of_lt (Real.exp_pos _)
  have hq1 : Real.exp (-sigma) < 1 := by
    rw [Real.exp_lt_one_iff]; linarith
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (a * M) (by norm_num : (1:ℝ) < 2)
  rw [← _root_.summable_nat_add_iff k]
  have hmaj : Summable (fun n : ℕ => 2 * a * M * Real.exp (-sigma) ^ (n + k)) := by
    have he : (fun n : ℕ => 2 * a * M * Real.exp (-sigma) ^ (n + k))
        = fun n : ℕ => (2 * a * M * Real.exp (-sigma) ^ k) * Real.exp (-sigma) ^ n := by
      funext n; rw [pow_add]; ring
    rw [he]
    exact (summable_geometric_of_lt_one hq0 hq1).mul_left _
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hmaj
  refine norm_hTerm_le hsig hM (le_of_lt (lt_of_lt_of_le hk ?_))
  exact pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (Nat.le_add_left k n)

/-- **THE POLE LATTICE, EXACTLY.**  `1 − 2e^{-s} = 0` precisely on `log 2 + 2πiℤ` — one Mathlib
lemma, not a theory. -/
theorem denom_eq_zero_iff (s : ℂ) :
    1 - 2 * Complex.exp (-s) = 0 ↔
      ∃ k : ℤ, s = (Real.log 2 : ℂ) + (k : ℂ) * (2 * Real.pi * Complex.I) := by
  have h2 : Complex.exp ((Real.log 2 : ℂ)) = 2 := by
    rw [← Complex.ofReal_exp, Real.exp_log (by norm_num : (0:ℝ) < 2)]
    norm_num
  have halg : (1 - 2 * Complex.exp (-s) = 0) ↔ Complex.exp (-s) = 1 / 2 := by
    constructor
    · intro h; linear_combination -h / 2
    · intro h; rw [h]; ring
  have hhalf : Complex.exp (-(Real.log 2 : ℂ)) = 1 / 2 := by
    rw [Complex.exp_neg, h2]
    norm_num
  rw [halg, ← hhalf, Complex.exp_eq_exp_iff_exists_int]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨-n, ?_⟩
    push_cast
    linear_combination -hn
  · rintro ⟨k, hk⟩
    refine ⟨-k, ?_⟩
    push_cast
    linear_combination -hk

/-- `D' = +2e^{-s}`, with NO minus sign.  Recorded because my first draft had it wrong and the
residue is `1` either way, so the error would have survived a read-through. -/
theorem deriv_denom (s : ℂ) :
    deriv (fun w : ℂ => 1 - 2 * Complex.exp (-w)) s = 2 * Complex.exp (-s) := by
  have h1 : HasDerivAt (fun w : ℂ => Complex.exp (-w)) (-Complex.exp (-s)) s := by
    simpa using (hasDerivAt_neg s).cexp
  have h2 : HasDerivAt (fun w : ℂ => 1 - 2 * Complex.exp (-w)) (2 * Complex.exp (-s)) s := by
    simpa using (h1.const_mul (2 : ℂ)).const_sub (1 : ℂ)
  exact h2.deriv

/-- **THE RESIDUE IS `1`** — literally, with no limit and no division by zero, because the
numerator and `D'` are the same expression. -/
theorem residue_eq_one (s : ℂ) (hs : 1 - 2 * Complex.exp (-s) = 0) :
    2 * Complex.exp (-s) / deriv (fun w : ℂ => 1 - 2 * Complex.exp (-w)) s = 1 := by
  rw [deriv_denom]
  have hne : 2 * Complex.exp (-s) ≠ 0 := by
    intro h
    rw [h] at hs
    norm_num at hs
  exact div_self hne

/-! ### The decomposition itself: `F = geometric + H` to the right of the convergence line

The source verifies its pole condition BY exhibiting this identity with `H` analytic past the line.
Everything in it is now a theorem except the analyticity of `H`, so this is the last *algebraic*
piece before `Adm` can be defined concretely instead of carried.

It reduces to a POINTWISE fact and one geometric series.  Since
`λₙ = n + a·2^{-n}`, splitting the exponential gives

    fTerm n s = (2e^{-s})^n + hTerm n s          (`fTerm_eq`, just `exp_add`)

and summing from `n = 1` turns the first part into `2e^{-s}·(1 − 2e^{-s})⁻¹`, convergent exactly
when `‖2e^{-s}‖ < 1`, i.e. `Re s > log 2` (`norm_two_exp_lt`) — which is the convergence line.

**WHAT THIS STILL DOES NOT GIVE.**  `Adm` remains carried.  Defining it concretely needs `H`
*analytic* on a half-plane, not merely summable, and that is a separate increment. -/

/-- The `n`th term of the Dirichlet generating function `F s = ∑_{n≥1} 2^n e^{-s λₙ}`. -/
noncomputable def fTerm (n : ℕ) (s : ℂ) : ℂ :=
  2 ^ n * Complex.exp (-s * ((lam n : ℝ) : ℂ))

/-- **THE POINTWISE SPLIT.**  Nothing analytic here — just `exp_add`. -/
theorem fTerm_eq (n : ℕ) (s : ℂ) :
    fTerm n s = (2 * Complex.exp (-s)) ^ n + hTerm n s := by
  have hcast : ((lam n : ℝ) : ℂ) = (n : ℂ) + (a : ℂ) / 2 ^ n := by
    simp only [lam]
    push_cast
    ring
  have hpow : (2 * Complex.exp (-s)) ^ n = 2 ^ n * Complex.exp (-(n : ℂ) * s) := by
    rw [mul_pow, ← Complex.exp_nat_mul]
    congr 1
    ring_nf
  have key : Complex.exp (-(n : ℂ) * s) * Complex.exp (-(a : ℂ) * s / 2 ^ n)
      = Complex.exp (-s * ((n : ℂ) + (a : ℂ) / 2 ^ n)) := by
    rw [← Complex.exp_add]
    congr 1
    ring_nf
  -- Rewriting `← key` first makes this a normalisation in the two atoms `exp (-n s)` and
  -- `exp (-a s / 2^n)`, rather than a `linear_combination` whose coefficient must be guessed.
  -- `ring_nf` not `ring`: `ring` here succeeds only via its own `ring_nf` fallback and then emits
  -- an INFO-level "Try this" advisory that an errors-and-warnings grep does not see.
  rw [fTerm, hTerm, hcast, hpow, ← key]
  ring_nf

/-- `‖2e^{-s}‖ < 1` exactly to the right of the convergence line `Re s = log 2`. -/
theorem norm_two_exp_lt {s : ℂ} (hs : Real.log 2 < s.re) : ‖2 * Complex.exp (-s)‖ < 1 := by
  rw [norm_mul, Complex.norm_exp]
  have h2 : ‖(2:ℂ)‖ = 2 := by norm_num
  rw [h2]
  have hhalf : Real.exp ((-s).re) < 1 / 2 := by
    have : (1:ℝ) / 2 = Real.exp (-(Real.log 2)) := by
      rw [Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ) < 2)]
      norm_num
    rw [this, Complex.neg_re]
    exact Real.exp_lt_exp.mpr (by linarith)
  linarith

/-- **THE DECOMPOSITION.**  `F = geometric + H` to the right of the convergence line, indexed from
`1` as the class is. -/
theorem dirichlet_decomp {s : ℂ} (hs : Real.log 2 < s.re) :
    ∑' n : ℕ, fTerm (n + 1) s
      = 2 * Complex.exp (-s) * (1 - 2 * Complex.exp (-s))⁻¹
        + ∑' n : ℕ, hTerm (n + 1) s := by
  have hnorm := norm_two_exp_lt hs
  have hgeo : HasSum (fun n : ℕ => (2 * Complex.exp (-s)) ^ (n + 1))
      (2 * Complex.exp (-s) * (1 - 2 * Complex.exp (-s))⁻¹) := by
    have h := (hasSum_geometric_of_norm_lt_one hnorm).mul_left (2 * Complex.exp (-s))
    have hfun2 : (fun n : ℕ => 2 * Complex.exp (-s) * (2 * Complex.exp (-s)) ^ n)
        = fun n : ℕ => (2 * Complex.exp (-s)) ^ (n + 1) := by
      funext n; rw [pow_succ]; ring
    rwa [hfun2] at h
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hspos : 0 < s.re := lt_trans hlog2 hs
  have hsum : Summable (fun n : ℕ => hTerm n s) :=
    Summable.of_norm (summable_norm_hTerm hspos (le_refl s.re) (le_refl ‖s‖))
  have hsum1 : Summable (fun n : ℕ => hTerm (n + 1) s) :=
    (_root_.summable_nat_add_iff 1).mpr hsum
  have hfun : (fun n : ℕ => fTerm (n + 1) s)
      = fun n : ℕ => (2 * Complex.exp (-s)) ^ (n + 1) + hTerm (n + 1) s := by
    funext n
    exact fTerm_eq (n + 1) s
  rw [hfun]
  exact (hgeo.add hsum1.hasSum).tsum_eq

/-! ### `H` analytic past the line, and `Adm` discharged

With `H` analytic where it needs to be, every clause of Conjecture 6's admissibility is a theorem,
so `Adm` can be DEFINED rather than carried.

`differentiableOn_hSum_halfplane` is the Dirichlet twin of `differentiableOn_gSum_ball`.  The bound
`2a‖s‖(e^{-σ})^n` depends on `‖s‖`, so the uniform bound
`Complex.differentiableOn_tsum_of_summable_norm` needs lives on `{Re s > σ} ∩ ball 0 M`
(`halfBall`), and locality lifts it to the open half-plane — which is why neither `σ` nor `M`
appears in the final statement.  Unlike `gTerm`, each `hTerm n` is ENTIRE, so the term-wise
differentiability is free.
**WHY THE ROW IS STILL NOT COUNTED, AND IT IS A NEW REASON.**  Until now the blocker was that `Adm`
was an obligation.  It is a theorem below.  What remains is narrower: the source's condition (2) is
worded *"the only singularities of the Dirichlet generating function on its convergence line are
`log(1/ρ) + 2πiℤ/ω`"*, and **nothing here formalises the word "singularity"**.  `Admissible` encodes
the DATA the source uses to establish that wording, so the step from the data to the
sentence is read by a human rather than by the elaborator.  That is an *unformalised interface* —
distinct from a carried hypothesis and from an uncovered case — and it is the one status left on
this row. -/
/-- A bounded piece of an open half-plane: where the `‖s‖`-dependent bound is uniform. -/
def halfBall (sigma M : ℝ) : Set ℂ := {s : ℂ | sigma < s.re} ∩ Metric.ball 0 M

theorem isOpen_halfBall (sigma M : ℝ) : IsOpen (halfBall sigma M) :=
  (isOpen_lt continuous_const Complex.continuous_re).inter Metric.isOpen_ball

/-- Each `hTerm n` is entire — an exponential of a linear function, no branch cut. -/
theorem differentiable_hTerm (n : ℕ) : Differentiable ℂ (hTerm n) := by
  have hfun : hTerm n = fun s : ℂ =>
      2 ^ n * Complex.exp (-(n : ℂ) * s) * (Complex.exp (-(a : ℂ) * s / 2 ^ n) - 1) := by
    funext s; rw [hTerm]
  rw [hfun]
  fun_prop

theorem differentiableOn_hSum {sigma M : ℝ} (hsig : 0 < sigma) :
    DifferentiableOn ℂ (fun s => ∑' n : ℕ, hTerm n s) (halfBall sigma M) := by
  -- No `0 ≤ M` is needed: the bound comes from MEMBERSHIP and `Summable.mul_left` needs no sign,
  -- so if `M < 0` the region is empty and every statement about it is vacuous.
  have hq0 : 0 ≤ Real.exp (-sigma) := le_of_lt (Real.exp_pos _)
  have hq1 : Real.exp (-sigma) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (a * M) (by norm_num : (1:ℝ) < 2)
  have hbnd : ∀ (n : ℕ) (w : ℂ), w ∈ halfBall sigma M →
      ‖hTerm (n + k) w‖ ≤ 2 * a * M * Real.exp (-sigma) ^ (n + k) := by
    intro n w hw
    have hre : sigma ≤ w.re := le_of_lt hw.1
    have hnm : ‖w‖ ≤ M := by
      have := hw.2
      simpa using le_of_lt (by simpa using this)
    refine norm_hTerm_le hre hnm ?_
    exact le_of_lt (lt_of_lt_of_le hk
      (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (Nat.le_add_left k n)))
  have hmaj : Summable (fun n : ℕ => 2 * a * M * Real.exp (-sigma) ^ (n + k)) := by
    have he : (fun n : ℕ => 2 * a * M * Real.exp (-sigma) ^ (n + k))
        = fun n : ℕ => (2 * a * M * Real.exp (-sigma) ^ k) * Real.exp (-sigma) ^ n := by
      funext n; rw [pow_add]; ring
    rw [he]
    exact (summable_geometric_of_lt_one hq0 hq1).mul_left _
  have hshift : DifferentiableOn ℂ (fun s => ∑' n : ℕ, hTerm (n + k) s) (halfBall sigma M) :=
    Complex.differentiableOn_tsum_of_summable_norm hmaj
      (fun n => (differentiable_hTerm (n + k)).differentiableOn) (isOpen_halfBall sigma M) hbnd
  have hhead : DifferentiableOn ℂ (fun s => ∑ n ∈ Finset.range k, hTerm n s)
      (halfBall sigma M) :=
    DifferentiableOn.fun_sum fun n _ => (differentiable_hTerm n).differentiableOn
  refine DifferentiableOn.congr (hhead.add hshift) ?_
  intro s hs
  have hre : sigma ≤ s.re := le_of_lt hs.1
  have hnm : ‖s‖ ≤ M := by
    have := hs.2
    simpa using le_of_lt (by simpa using this)
  have hsum : Summable (fun n : ℕ => hTerm n s) :=
    Summable.of_norm (summable_norm_hTerm hsig hre hnm)
  exact (hsum.sum_add_tsum_nat_add k).symm

/-- **`H` IS DIFFERENTIABLE ON THE WHOLE OPEN HALF-PLANE `Re s > 0`** — strictly past the
convergence line `Re s = log 2`. -/
theorem differentiableOn_hSum_halfplane :
    DifferentiableOn ℂ (fun s => ∑' n : ℕ, hTerm n s) {s : ℂ | 0 < s.re} := by
  intro s hs
  have hs0 : 0 < s.re := hs
  have hmem : s ∈ halfBall (s.re / 2) (‖s‖ + 1) := by
    refine ⟨by simp; linarith, ?_⟩
    simp only [Metric.mem_ball, Complex.dist_eq, sub_zero]
    linarith
  have hnhds := (isOpen_halfBall (s.re / 2) (‖s‖ + 1)).mem_nhds hmem
  exact ((differentiableOn_hSum (by linarith : (0:ℝ) < s.re / 2)).differentiableAt
    hnhds).differentiableWithinAt

/-! ### The word "singularity", formalised

Admissibility condition (2) reads *"the only singularities of the Dirichlet generating function on
its convergence line are `log(1/ρ) + 2πiℤ/ω"*.  Everything above is the DATA the source uses to
establish that sentence; this section states the sentence.

**What the condition actually asks is CONFINEMENT** — that no singularity lies outside the lattice —
so the content is that the series continues analytically across every point of the half-plane that
is *not* a lattice point, with "singularity" spelled as failure of `DifferentiableAt`.  That each
lattice point IS singular is a separate and true statement which admissibility does not need, and
the direction matters: a class with FEWER singularities still satisfies the condition, so
confinement is the safe half for exhibiting an admissible class.

Two deliberate strengthenings, both in the harmless direction.  The source speaks of the convergence
line; `no_singularity_off_lattice` covers the whole open half-plane `Re s > 0`, which contains it.
And `Fc_eq_series` pins the continuation to the right function, so this is not the analyticity of
some unrelated `Fc`. -/

/-- The analytic continuation of the Dirichlet series, read off the decomposition. -/
noncomputable def Fc (s : ℂ) : ℂ :=
  2 * Complex.exp (-s) * (1 - 2 * Complex.exp (-s))⁻¹ + ∑' n : ℕ, hTerm (n + 1) s

theorem isOpen_rePos : IsOpen {s : ℂ | 0 < s.re} :=
  isOpen_lt continuous_const Complex.continuous_re

/-- The corrector indexed from `1` is the one indexed from `0` minus its `n = 0` term. -/
theorem hShift_eq {s : ℂ} (h0 : 0 < s.re) :
    ∑' n : ℕ, hTerm (n + 1) s = (∑' n : ℕ, hTerm n s) - hTerm 0 s := by
  have hsum : Summable (fun n : ℕ => hTerm n s) :=
    Summable.of_norm (summable_norm_hTerm h0 (le_refl s.re) (le_refl ‖s‖))
  rw [hsum.tsum_eq_zero_add]
  ring

/-- `H` indexed from `1` — the form the decomposition uses — is differentiable on `Re s > 0`. -/
theorem hShift_diff :
    DifferentiableOn ℂ (fun s => ∑' n : ℕ, hTerm (n + 1) s) {s : ℂ | 0 < s.re} := by
  have h : DifferentiableOn ℂ (fun s => (∑' n : ℕ, hTerm n s) - hTerm 0 s)
      {s : ℂ | 0 < s.re} :=
    differentiableOn_hSum_halfplane.sub (differentiable_hTerm 0).differentiableOn
  exact h.congr (fun s hs => hShift_eq hs)

/-- The geometric part is differentiable wherever its denominator does not vanish. -/
theorem diff_rational {s : ℂ} (hs : 1 - 2 * Complex.exp (-s) ≠ 0) :
    DifferentiableAt ℂ (fun w : ℂ => 2 * Complex.exp (-w) * (1 - 2 * Complex.exp (-w))⁻¹) s := by
  have he : DifferentiableAt ℂ (fun w : ℂ => Complex.exp (-w)) s := by fun_prop
  have hd : DifferentiableAt ℂ (fun w : ℂ => 1 - 2 * Complex.exp (-w)) s := by fun_prop
  exact (he.const_mul 2).mul (hd.inv hs)

/-- **NO SINGULARITY OFF THE LATTICE.**  At every point of `Re s > 0` that is not of the form
`log 2 + 2πik`, the continuation is differentiable — so the generating function has no singularity
there.  This is admissibility condition (2)'s content. -/
theorem no_singularity_off_lattice {s : ℂ} (h0 : 0 < s.re)
    (hs : ¬ ∃ k : ℤ, s = (Real.log 2 : ℂ) + (k : ℂ) * (2 * Real.pi * Complex.I)) :
    DifferentiableAt ℂ Fc s := by
  have hden : 1 - 2 * Complex.exp (-s) ≠ 0 := fun h => hs ((denom_eq_zero_iff s).mp h)
  have hH : DifferentiableAt ℂ (fun w => ∑' n : ℕ, hTerm (n + 1) w) s :=
    hShift_diff.differentiableAt (isOpen_rePos.mem_nhds h0)
  exact (diff_rational hden).add hH

/-- **THE CONTINUATION IS A CONTINUATION OF THE RIGHT FUNCTION** — it agrees with the Dirichlet
series wherever that series converges. -/
theorem Fc_eq_series {s : ℂ} (hs : Real.log 2 < s.re) :
    Fc s = ∑' n : ℕ, fTerm (n + 1) s :=
  (dirichlet_decomp hs).symm

/-! ### The second reading: every lattice point really IS a singularity

`no_singularity_off_lattice` above gives CONFINEMENT — no singularity outside the lattice — which is
one reading of *"the only singularities are `Λ`"*.  The campaign's rules require proving BOTH
readings when a sentence admits two, and under SET EQUALITY the condition also asserts that each
lattice point is a singularity.  Neither the confinement clause nor the old data clauses
gave that: the exact zero set of the DENOMINATOR makes a pole overwhelmingly likely, but it
is not non-analyticity of `Fc`.

**The argument avoids limits of norms entirely.**  Multiply through by the denominator.  On a
punctured ball `D·Fc = 2e^{−s} + D·H`, whose limit at `λ` is `2e^{−λ} ≠ 0`; but if `Fc` were
continuous at `λ` then `D·Fc → D(λ)·Fc(λ) = 0`.  Two limits of one function along one filter, so
`Fc` is not continuous and a fortiori not differentiable.  Note `Fc λ` is a perfectly ordinary value
in Lean — `(0 : ℂ)⁻¹` is `0` — so nothing is wrong with `Fc` AT the point; the content is entirely
about its behaviour NEAR it.

The punctured ball comes from `lattice_separated`: two lattice points differ by `2πik`, so any two
within distance `2π` coincide. -/

/-- **THE LATTICE IS `2*pi`-SEPARATED.**  Two points of `log 2 + 2*pi*i*Z` at distance less than
`2*pi` coincide. -/
theorem lattice_separated {s lam : ℂ}
    (hs : ∃ k : ℤ, s = (Real.log 2 : ℂ) + (k : ℂ) * (2 * Real.pi * Complex.I))
    (hl : ∃ m : ℤ, lam = (Real.log 2 : ℂ) + (m : ℂ) * (2 * Real.pi * Complex.I))
    (hd : ‖s - lam‖ < 2 * Real.pi) : s = lam := by
  obtain ⟨k, hk⟩ := hs
  obtain ⟨m, hm⟩ := hl
  by_contra hne
  have hkm : k ≠ m := by
    intro h
    exact hne (by rw [hk, hm, h])
  have hdiff : s - lam = ((k : ℂ) - (m : ℂ)) * (2 * Real.pi * Complex.I) := by
    rw [hk, hm]; ring
  have hone : (1 : ℝ) ≤ |((k : ℝ) - (m : ℝ))| := by
    have : ((k : ℤ) - m) ≠ 0 := sub_ne_zero_of_ne hkm
    have h1 : (1 : ℤ) ≤ |(k : ℤ) - m| := Int.one_le_abs this
    calc (1 : ℝ) = ((1 : ℤ) : ℝ) := by norm_num
      _ ≤ ((|(k : ℤ) - m| : ℤ) : ℝ) := by exact_mod_cast h1
      _ = |((k : ℝ) - (m : ℝ))| := by push_cast [Int.cast_abs]; ring_nf
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hnorm : ‖s - lam‖ = |((k : ℝ) - (m : ℝ))| * (2 * Real.pi) := by
    rw [hdiff]
    have hc : ((k : ℂ) - (m : ℂ)) = (((k : ℝ) - (m : ℝ) : ℝ) : ℂ) := by push_cast; ring
    rw [hc, norm_mul, Complex.norm_real, norm_mul, norm_mul]
    simp [Complex.norm_I, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [hnorm] at hd
  nlinarith [hd, hone, hpi]

/-- The denominator is nonzero on the punctured ball of radius `2*pi` about a lattice point. -/
theorem denom_ne_on_punctured {lam : ℂ}
    (hl : ∃ m : ℤ, lam = (Real.log 2 : ℂ) + (m : ℂ) * (2 * Real.pi * Complex.I))
    {s : ℂ} (hs : s ≠ lam) (hd : ‖s - lam‖ < 2 * Real.pi) :
    1 - 2 * Complex.exp (-s) ≠ 0 := by
  intro h
  exact hs (lattice_separated ((denom_eq_zero_iff s).mp h) hl hd)

/-- The punctured ball of radius `2*pi` about a lattice point lies in `𝓝[≠] lam`. -/
theorem eventually_punctured {lam : ℂ} :
    ∀ᶠ s in 𝓝[≠] lam, s ≠ lam ∧ ‖s - lam‖ < 2 * Real.pi := by
  have hball : ∀ᶠ s in 𝓝 lam, ‖s - lam‖ < 2 * Real.pi := by
    have : Metric.ball lam (2 * Real.pi) ∈ 𝓝 lam :=
      Metric.ball_mem_nhds lam (by positivity)
    filter_upwards [this] with s hs
    simpa [Complex.dist_eq] using hs
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hball] with s h1 h2
  exact ⟨h1, h2⟩

/-- **EVERY LATTICE POINT IS A SINGULARITY.**  `Fc` is not differentiable at any
`log 2 + 2*pi*i*k` — indeed not even continuous there.  With `no_singularity_off_lattice` this makes
the singularity set EXACTLY the lattice, which is the set-equality reading of condition (2). -/
theorem not_differentiableAt_lattice {lam : ℂ}
    (hl : ∃ m : ℤ, lam = (Real.log 2 : ℂ) + (m : ℂ) * (2 * Real.pi * Complex.I)) :
    ¬ DifferentiableAt ℂ Fc lam := by
  intro hdiff
  have hcont : ContinuousAt Fc lam := hdiff.continuousAt
  have hD0 : 1 - 2 * Complex.exp (-lam) = 0 := (denom_eq_zero_iff lam).mpr hl
  have hDcont : ContinuousAt (fun s : ℂ => 1 - 2 * Complex.exp (-s)) lam := by fun_prop
  -- limit 1: continuity forces `D * Fc -> D lam * Fc lam = 0`
  have lim1 : Tendsto (fun s : ℂ => (1 - 2 * Complex.exp (-s)) * Fc s) (𝓝[≠] lam) (𝓝 0) := by
    have h : Tendsto (fun s : ℂ => (1 - 2 * Complex.exp (-s)) * Fc s) (𝓝 lam)
        (𝓝 ((1 - 2 * Complex.exp (-lam)) * Fc lam)) := (hDcont.mul hcont).tendsto
    rw [hD0, zero_mul] at h
    exact h.mono_left nhdsWithin_le_nhds
  -- lam is in the open half-plane, so `H` is continuous there
  have hlam_re : 0 < lam.re := by
    obtain ⟨m, hm⟩ := hl
    have him : ((m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)).re = 0 := by
      simp [Complex.mul_re, Complex.I_re, Complex.I_im]
    have hre : lam.re = Real.log 2 := by
      rw [hm, Complex.add_re, Complex.ofReal_re, him, add_zero]
    rw [hre]; exact Real.log_pos (by norm_num)
  have hHcont : ContinuousAt (fun s : ℂ => ∑' n : ℕ, hTerm (n + 1) s) lam :=
    (hShift_diff.differentiableAt (isOpen_rePos.mem_nhds hlam_re)).continuousAt
  -- limit 2: on the punctured ball `D * Fc = 2e^-s + D * H -> 2e^-lam`
  have heq : ∀ᶠ s in 𝓝[≠] lam, (1 - 2 * Complex.exp (-s)) * Fc s
      = 2 * Complex.exp (-s) + (1 - 2 * Complex.exp (-s)) * (∑' n : ℕ, hTerm (n + 1) s) := by
    filter_upwards [eventually_punctured (lam := lam)] with s hs
    have hne : 1 - 2 * Complex.exp (-s) ≠ 0 := denom_ne_on_punctured hl hs.1 hs.2
    rw [Fc]
    field_simp
  have lim2 : Tendsto (fun s : ℂ => (1 - 2 * Complex.exp (-s)) * Fc s) (𝓝[≠] lam)
      (𝓝 (2 * Complex.exp (-lam))) := by
    have hN : ContinuousAt (fun s : ℂ => 2 * Complex.exp (-s)) lam := by fun_prop
    have h : Tendsto (fun s : ℂ => 2 * Complex.exp (-s)
        + (1 - 2 * Complex.exp (-s)) * (∑' n : ℕ, hTerm (n + 1) s)) (𝓝 lam)
        (𝓝 (2 * Complex.exp (-lam)
          + (1 - 2 * Complex.exp (-lam)) * (∑' n : ℕ, hTerm (n + 1) lam))) :=
      (hN.add (hDcont.mul hHcont)).tendsto
    rw [hD0, zero_mul, add_zero] at h
    exact (tendsto_congr' heq).mpr (h.mono_left nhdsWithin_le_nhds)
  -- two limits, one filter
  have hne : 2 * Complex.exp (-lam) ≠ 0 := by
    intro h
    rw [h] at hD0
    norm_num at hD0
  exact hne (tendsto_nhds_unique lim2 lim1)

/-- **CONJECTURE 6'S ADMISSIBILITY, FOR THIS CLASS, IN THE SOURCE'S OWN WORDING.**

Condition (1) is that the power-series corrector is analytic on the cut disk past `ρ`; condition (2)
is *"the only singularities of the Dirichlet generating function on its convergence line are
`log(1/ρ) + 2πiℤ/ω`"*.  Both are stated here as what they say.

**History, because the wording was the row's last residue.**  This definition once listed the DATA
the source uses to verify condition (2) — the decomposition, the analyticity of `H`, the exact zero
set — and the step from that data to the source's sentence was read by a human, because nothing
formalised the word "singularity".  It is formalised now, and in BOTH readings of *"the only
singularities are Λ"*, which the campaign's rules require when a definition admits two:

* **confinement** — `no_singularity_off_lattice`: at every point of `Re s > 0` off the lattice the
  continuation is differentiable, so no singularity lies outside `Λ`;
* **set equality** — `not_differentiableAt_lattice`: at every lattice point it is not differentiable
  (not even continuous), so every point of `Λ` really is one.

Together the singularity set is EXACTLY `Λ`, and `Fc_eq_series` pins the continuation to the
Dirichlet series wherever that series converges, so these are statements about the right function.

**One deliberate strengthening remains, and it is harmless in this direction.**  The source speaks
of the convergence line; clauses (2) and (3) here range over the whole half-plane `Re s > 0`, which
contains it.  That makes the exhibited class *more* admissible, and for refuting *"every admissible
class satisfies P"* what is needed is one class that IS admissible — so the refutation is valid a
fortiori.  The direction is the whole question: a transcription WEAKER than the source's condition
would leave `admissible` failing to establish that this class is one the conjecture speaks about. -/
def Admissible : Prop :=
  (∀ r : ℝ, r < 1 → DifferentiableOn ℂ (fun z => ∑' n : ℕ, gTerm n z)
      (Complex.slitPlane ∩ Metric.ball 0 r))
  ∧ (∀ s : ℂ, Real.log 2 < s.re → Fc s = ∑' n : ℕ, fTerm (n + 1) s)
  ∧ (∀ s : ℂ, 0 < s.re →
      (¬ ∃ k : ℤ, s = (Real.log 2 : ℂ) + (k : ℂ) * (2 * Real.pi * Complex.I)) →
      DifferentiableAt ℂ Fc s)
  ∧ (∀ s : ℂ, (∃ k : ℤ, s = (Real.log 2 : ℂ) + (k : ℂ) * (2 * Real.pi * Complex.I)) →
      ¬ DifferentiableAt ℂ Fc s)

/-- **THE CLASS IS ADMISSIBLE** — every clause is one of the theorems above. -/
theorem admissible : Admissible :=
  ⟨fun _ hr => differentiableOn_gSum_ball hr,
   fun _ hs => Fc_eq_series hs,
   fun _ h0 hs => no_singularity_off_lattice h0 hs,
   fun _ hs => not_differentiableAt_lattice hs⟩

/-- **CONJECTURE 6 IS REFUTED FOR THIS CLASS, WITH NOTHING CARRIED.**  Compare
`conjecture_6_false`, which needed `Adm` supplied; here it is discharged by `admissible`. -/
theorem conjecture_6_false_unconditional (h : Conj6 Admissible) : False :=
  conjecture_6_false Admissible admissible h

end Principia.MathDB.P366299
