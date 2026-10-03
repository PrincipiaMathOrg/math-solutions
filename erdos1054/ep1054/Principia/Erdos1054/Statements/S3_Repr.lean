/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Erdos1054.Defs
import Principia.Erdos1054.Statements.Inputs
import Principia.Erdos1054.Statements.S1_Main

set_option autoImplicit false

/-!
# Erdős 1054 (EP1054.tex) §3 "Representability" — statements only

Paper lines 642–982 of `Campaigns/Erdos-1054/collab-paper/EP1054.tex`. Every result is a
`def … : Prop`; **nothing is asserted here**. Proofs come later and take the `Inputs` names
(`Cite_*`, `Comp_*`) as hypotheses.

## What is in the section

* `lem:analytic-odd-representability` — almost every odd integer is represented (MV exceptional set).
* `thm:fraiture-representability` — `𝓡 = ℕ ∖ {2, 5}`: the same statement as the intro's
  `eq:exact-representability` (lines 114–115, used by `prop:tightness-equivalence` at line 2695),
  so `Thm_FraitureRepresentability` is an `abbrev` of `S1_Main`'s `Eq_ExactRepresentability`
  (one body, two paper labels; `S1_Main` is imported for that alone).
* `lem:fraiture-prime-window`, `lem:fraiture-extension` — the two elementary tools of the finite
  range (subset sums of primes in a window `(M, Y]`, `Y < M²`, are prefix sums after adding `1`).
* `prop:fraiture-finite` — three intervals, **one `Prop` each** (`Eq_FraitureSmall`,
  `Eq_FraitureFirstWindow`, `Eq_FraitureLargeWindow`), resting on the three verifier checks
  `Comp_Verifier_*` and Dusart.
* `lem:fraiture-balanced-goldbach` — the balanced statement, proved in the paper from Helfgott's
  weighted bound (`Cite_Helfgott_weighted`) and Rosser–Schoenfeld (`Cite_RosserSchoenfeld_psi`).
* `prop:fraiture-tail` — every `n ≥ 10^27 + 10^8` is represented.
* the closing remark — encoded as the dependency claim it makes (`Rem_FraitureCheckUsage`).

Unlabelled proof steps that carry a checkable claim of their own are `Step_*` defs (with their
line numbers), so the spine can split a proof exactly where the paper does.

## Encoding conventions used throughout

* `R` is the paper's `𝓡` (`Defs.R`); `0 ∉ R` holds because every prefix sum starts with the
  divisor `1`, so a statement about "represented positive integers" is a statement about `R`.
* Interval endpoints are natural-number literals (`10 ^ 7 = 10 000 000`).
* A finite set of distinct primes is a `Finset ℕ`; "subset sums" is `subsetSums` below, which
  contains `0` (empty subset), exactly as the paper's recurrence `S_0 = {0}` (line 761).
-/

namespace Principia.Erdos1054

open Finset

/-! ## Lemma `lem:analytic-odd-representability` (lines 651–670) -/

/-- The odd unrepresented integers `{n : n odd, n ∉ 𝓡}` (EP1054.tex line 655). `0` is not odd,
so `cnt oddUnrep X` is exactly the paper's `#{n ≤ X : n odd, n ∉ 𝓡}`. -/
def oddUnrep : Set ℕ := {n | Odd n ∧ n ∉ R}

-- deps: Cite_MV_exceptional (even `n ≤ X` not a sum of two primes: `O(X^{1-c})`);
--       Mathlib `Chebyshev.pi_le_log4_mul_div` (the discarded `n = 2p ≤ X` number
--       `π(X/2) ≪ X/log X`); the elementary fact that the divisors of `pq` (`p < q` primes) are
--       `1, p, q, pq`, so `1 + p + q ∈ 𝓡`; translate by `1`.
-- used by: Lem_AnalyticOddRepresentability_LittleO.
/-- `lem:analytic-odd-representability`, EP1054.tex line 651, **main bound**.
"There is an absolute $c>0$ such that, for $X\geq3$,
\[ \#\{n\leq X:n\text{ odd},\ n\notin\Rcal\} \ll X^{1-c}+\frac{X}{\log X}. \]"

Encoding: `∃ c > 0, ∃ C` (both absolute, so quantified before `X`), `∀ X ≥ 3`,
`cnt oddUnrep X ≤ C (X^{1-c} + X/log X)`. Real `rpow`; `log X > 0` on the range. -/
def Lem_AnalyticOddRepresentability_Bound : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, ∀ X : ℝ, 3 ≤ X →
    (cnt oddUnrep X : ℝ) ≤ C * (X ^ (1 - c) + X / Real.log X)

-- deps: Lem_AnalyticOddRepresentability_Bound; elementary asymptotics
--       (`X^{1-c} + X/log X = o(X/log log log X)`).
-- used by: proof of thm:almost-log-tail (line 2085–2086), proof of thm:subexp-growth
--          (lines 2221–2222) — both use exactly this `o(X/log log log X)` form.
/-- `lem:analytic-odd-representability`, EP1054.tex line 658, **"in particular" clause**.
"In particular, this exceptional set has size $o(X/\log\log\log X)$ as $X\to\infty$."

Encoding: `∀ ε > 0, ∃ X₀, ∀ X ≥ X₀, cnt oddUnrep X ≤ ε · X / log₃ X`, with `log₃ = logIt 3`
(positive for large `X`, so the bound is meaningful on the range `X ≥ X₀`). -/
def Lem_AnalyticOddRepresentability_LittleO : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
    (cnt oddUnrep X : ℝ) ≤ ε * (X / logIt 3 X)

-- deps: Lem_AnalyticOddRepresentability_Bound, Lem_AnalyticOddRepresentability_LittleO.
/-- `lem:analytic-odd-representability`, EP1054.tex lines 651–660, the full lemma: the main
bound together with its "in particular" clause. -/
def Lem_AnalyticOddRepresentability : Prop :=
  Lem_AnalyticOddRepresentability_Bound ∧ Lem_AnalyticOddRepresentability_LittleO

/-! ## The two elementary tools (lines 686–722) -/

/-- The subset sums of a finite set of naturals, `{∑_{p ∈ S} p : S ⊆ P}` (lines 712–715).
The empty subset contributes `0`, matching the paper's recurrence `S_0 = {0}`,
`S_j = S_{j-1} ∪ (S_{j-1} + p_j)` (line 761). `N ∈ subsetSums P` unfolds to exactly the shape
`∃ S ⊆ P, ∑ p ∈ S, p = N` used by `Comp_Verifier_window1`. -/
def subsetSums (P : Finset ℕ) : Set ℕ := {N | ∃ S ⊆ P, ∑ p ∈ S, p = N}

-- deps: none beyond elementary divisor combinatorics (every composite divisor of `∏_{j∈J} p_j`
--       exceeds `M² > Y`, so the divisors begin `1, p_j (j ∈ J)` in increasing order).
-- used by: Eq_FraitureFirstWindow (line 768), Eq_FraitureLargeWindow (line 821).
/-- `lem:fraiture-prime-window`, EP1054.tex line 690.
"Let $M>1$, and suppose that $M<p_1<\cdots<p_t\leq Y<M^2$ are distinct primes. If
$J\subseteq\{1,\ldots,t\}$ is nonempty, then \[ 1+\sum_{j\in J}p_j\in\Rcal. \]"

Encoding: the primes `p_1 < ⋯ < p_t` are a `Finset ℕ` `P` (distinctness and the ordering carry
no content beyond membership); `J` is a nonempty sub-`Finset`. `M` and `Y` are **real**, as in the
paper ("Let $M>1$", no integrality). A natural-number `M` would be strictly weaker: it only
reaches windows with `p_t < (p_1 - 1)^2`, while the real form reaches every `p_t < p_1^2`
(e.g. `P = J = {11, 109}`, `M = 10.5`, `Y = 109 < 110.25`, which gives `121 ∈ 𝓡` from `m = 1199`,
and no natural `M < 11` has `M² > 109`). Both consumers instantiate with casts of integers
(`M = 10 000, Y = 99 000 000`; `M = 20 000 000, Y = 399 000 000 000 000`). -/
def Lem_FraiturePrimeWindow : Prop :=
  ∀ (M Y : ℝ) (P : Finset ℕ), 1 < M → Y < M ^ 2 →
    (∀ p ∈ P, p.Prime ∧ M < (p : ℝ) ∧ (p : ℝ) ≤ Y) →
    ∀ J ⊆ P, J.Nonempty → (1 + ∑ p ∈ J, p) ∈ R

-- deps: none (two integer intervals `[C, U]` and `[C + p, U + p]` overlap or abut when
--       `C + p ≤ U + 1`).
-- used by: Step_FraitureFirstWindowCover (line 762), Step_FraitureLargeWindowCover (line 789).
/-- `lem:fraiture-extension`, EP1054.tex line 710.
"Let $C\leq U$ be integers. Suppose that the subset sums of a finite set of distinct primes contain
every integer in $[C,U]$, and let $p$ be a new prime satisfying $p\leq U-C+1$. After adjoining $p$,
the subset sums contain every integer in $[C,U+p]$."

Encoding: `C U : ℕ`. Taking them in `ℤ` adds nothing: subset sums are `≥ 0`, so a negative `C`
makes the covering hypothesis false. `U − C + 1` is exact in `ℕ` because `C ≤ U` is a hypothesis.
"New prime" is `p ∉ P` (needed: re-adjoining an old prime adds no sums). Primality of `P` and `p`
is kept although the proof does not use it (dropping a hypothesis would change the statement). -/
def Lem_FraitureExtension : Prop :=
  ∀ (C U : ℕ) (P : Finset ℕ) (p : ℕ), C ≤ U → (∀ q ∈ P, q.Prime) →
    (∀ N : ℕ, C ≤ N → N ≤ U → N ∈ subsetSums P) →
    p.Prime → p ∉ P → p ≤ U - C + 1 →
    ∀ N : ℕ, C ≤ N → N ≤ U + p → N ∈ subsetSums (insert p P)

/-! ## Proposition `prop:fraiture-finite` (lines 726–823): the three finite intervals -/

-- deps: elementary divisor ordering (`q > B` prime, so the divisors of `Bq` are those of `B`,
--       then `q` times those of `B`, in the same order).
-- used by: Eq_FraitureSmall (with Comp_Verifier_small).
/-- PROOF STEP of `prop:fraiture-finite`, EP1054.tex lines 746–752 (not a paper environment).
"take $1\leq B\leq1000$ and a prime $q>B$. The divisors of $Bq$ consist first of the divisors of
$B$ and then of $q$ times those divisors, in the same order. Thus every integer of the form
\[ \sigma(B)+q\sum_{i=1}^j d_i(B), \quad 1\leq j\leq\tau(B), \] is represented."

Encoding: `∑_{i=1}^{j} d_i(B)` is `prefixSumDivisors B j`; the witness is `m = Bq`, prefix length
`τ(B) + j`. Stated as membership in `R`, as the paper says ("is represented"); the range
`B ≤ 1000` is the paper's (the claim holds for every `B ≥ 1`). -/
def Step_FraitureSmallBq : Prop :=
  ∀ B q j : ℕ, 1 ≤ B → B ≤ 1000 → q.Prime → B < q → 1 ≤ j → j ≤ B.divisors.card →
    sig B + q * prefixSumDivisors B j ∈ R

-- deps: none (the divisors of `4` are `1, 2, 4`).
-- used by: Eq_FraitureSmall.
/-- PROOF STEP of `prop:fraiture-finite`, EP1054.tex lines 754–755 (not a paper environment).
"except $7$, which has the separate representation $7=1+2+4$ from $n=4$." -/
def Step_FraitureSeven : Prop := IsRep 7 4

-- deps: Comp_Verifier_small (check 1: every `N ∈ [6, 10^7]`, `N ≠ 7`, has the form of
--       Step_FraitureSmallBq), Step_FraitureSmallBq, Step_FraitureSeven.
-- used by: Prop_FraitureFinite, Thm_FraitureRepresentability.
/-- `eq:fraiture-small` — `prop:fraiture-finite`, first interval, EP1054.tex lines 728–731.
"Every positive integer in each of the following intervals is represented: $[6,10\,000\,000]$". -/
def Eq_FraitureSmall : Prop :=
  ∀ N : ℕ, 6 ≤ N → N ≤ 10 ^ 7 → N ∈ R

-- deps: Comp_Verifier_window1 (check 2: the 94 primes in `(10000, 10883]` cover
--       `[469615, 480503]`; the extension hypothesis holds for every prime through `98 999 987`;
--       the final upper end is `273 803 744 799 153`); Lem_FraitureExtension, applied by induction
--       over the primes of `(10883, 98999987]` in increasing order.
-- used by: Eq_FraitureFirstWindow.
/-- PROOF STEP of `prop:fraiture-finite`, EP1054.tex lines 757–767 (not a paper environment).
"The first $94$ primes in $(M,Y]$, lying between $10\,007$ and $10\,883$, have subset sums covering
$[469\,615,480\,503]$. … The verifier checks the hypothesis of Lemma fraiture-extension for each
successive prime through $98\,999\,987$. The resulting subset-sum interval is
\[ [469\,615,273\,803\,744\,799\,153]. \]"

Encoding: the primes used are those in `(10 000, 98 999 987]`, all `≤ Y = 99 000 000`. -/
def Step_FraitureFirstWindowCover : Prop :=
  ∀ N : ℕ, 469615 ≤ N → N ≤ 273803744799153 →
    N ∈ subsetSums ((Finset.Ioc 10000 98999987).filter Nat.Prime)

-- deps: Step_FraitureFirstWindowCover; Lem_FraiturePrimeWindow with `M = (10 000 : ℝ)`,
--       `Y = (99 000 000 : ℝ) < M² = 10^8` (a covered `N ≥ 469615` is a nonempty subset sum).
-- used by: Prop_FraitureFinite, Thm_FraitureRepresentability.
/-- `eq:fraiture-first-window` — `prop:fraiture-finite`, second interval, EP1054.tex lines 732–733.
"Every positive integer in each of the following intervals is represented:
$[469\,616,273\,803\,744\,799\,154]$". -/
def Eq_FraitureFirstWindow : Prop :=
  ∀ N : ℕ, 469616 ≤ N → N ≤ 273803744799154 → N ∈ R

-- deps: Comp_Verifier_largeSeed (check 3: every integer of `[105 000 000, 156 000 000]` is a sum
--       of 4 or 5 distinct primes in `(2·10^7, 4·10^7)`); Lem_FraitureExtension by induction over
--       the primes of `(4·10^7, 399·10^12]` in increasing order — the first, `40 000 003`, is
--       `≤ 51 000 001 = U − C + 1`, and after adjoining `p` the width is `≥ 2p`, so Bertrand
--       (Mathlib `Nat.exists_prime_lt_and_le_two_mul`) keeps the hypothesis `p' ≤ U − C + 1`.
-- used by: Eq_FraitureLargeWindow.
/-- PROOF STEP of `prop:fraiture-finite`, EP1054.tex lines 771–792 and 820 (not a paper
environment). "let $M=20\,000\,000$. For every one of the $51\,000\,001$ integers in
$[105\,000\,000,156\,000\,000]$, the verifier constructs and checks a sum of four or five distinct
primes in $(M,2M)$. … The next prime after $2M$ is $40\,000\,003$, which is at most the inclusive
width $51\,000\,001$ of the certified interval. Thus Lemma fraiture-extension starts the
interval-extension induction. After a prime $p$ has been adjoined, the new interval width is at
least $2p$, while Bertrand's postulate supplies the next prime below $2p$; the induction therefore
continues for every subsequent prime."

Encoding: the extension runs through every prime `2M < p ≤ Y = 399 000 000 000 000`, so the
upper end becomes `156 000 000 + ∑_{2M < p ≤ Y} p`. The seed primes `(M, 2M)` and the adjoined
primes `(2M, Y]` together are the primes of `(M, Y]` (`2M = 40 000 000` is not prime). -/
def Step_FraitureLargeWindowCover : Prop :=
  ∀ N : ℕ, 105000000 ≤ N →
    N ≤ 156000000 + (∑ p ∈ (Finset.Ioc 40000000 399000000000000).filter Nat.Prime, p) →
    N ∈ subsetSums ((Finset.Ioc 20000000 399000000000000).filter Nat.Prime)

-- deps: Cite_Dusart_Thm69 (at `x = a` and `x = Y`); `2.71 < e < 2.72` (Mathlib
--       `Real.exp_one_gt_d9`, `Real.exp_one_lt_d9`) with the rational comparisons
--       `2.72^32 < a` and `Y < 2.71^34` (so `log a > 32`, `log Y < 34`); rational arithmetic.
-- used by: Eq_FraitureLargeWindow.
/-- PROOF STEP of `prop:fraiture-finite`, EP1054.tex lines 794–819 (not a paper environment).
"Set $Y=399\,000\,000\,000\,000<M^2$. It remains to show that
\[ \sum_{2M<p\leq Y}p>10^{27}+10^8. \]"
The paper's chain (lines 798–813), with `a = Y/2 = 199 500 000 000 000`:
`x/log x < π(x) ≤ x/log x (1 + 1.2762/log x) < 1.05 x/log x` for `x ≥ a`, and
`∑_{2M<p≤Y} p ≥ a(π(Y) − π(a)) > a(Y/34 − 1.05a/32)
 = 17 599 173 046 875 000 000 000 000 000/17 > 1.03·10^27 > 10^27 + 10^8`. -/
def Step_FraitureLargePrimeSum : Prop :=
  10 ^ 27 + 10 ^ 8 < ∑ p ∈ (Finset.Ioc 40000000 399000000000000).filter Nat.Prime, p

-- deps: Step_FraitureLargeWindowCover, Step_FraitureLargePrimeSum; Lem_FraiturePrimeWindow with
--       `M = (20 000 000 : ℝ)`, `Y = (399 000 000 000 000 : ℝ) < M² = 4·10^14`.
-- used by: Prop_FraitureFinite, Thm_FraitureRepresentability.
/-- `eq:fraiture-large-window` — `prop:fraiture-finite`, third interval, EP1054.tex lines 734–735.
"Every positive integer in each of the following intervals is represented:
$[105\,000\,001,10^{27}+10^8]$". -/
def Eq_FraitureLargeWindow : Prop :=
  ∀ N : ℕ, 105000001 ≤ N → N ≤ 10 ^ 27 + 10 ^ 8 → N ∈ R

-- deps: Eq_FraitureSmall, Eq_FraitureFirstWindow, Eq_FraitureLargeWindow (hence, transitively:
--       Comp_Verifier_small, Comp_Verifier_window1, Comp_Verifier_largeSeed, Cite_Dusart_Thm69,
--       Lem_FraiturePrimeWindow, Lem_FraitureExtension, Bertrand).
-- used by: Thm_FraitureRepresentability.
/-- `prop:fraiture-finite`, EP1054.tex line 726.
"Every positive integer in each of the following intervals is represented:
\begin{align} &[6,10\,000\,000], \label{eq:fraiture-small}\\
&[469\,616,273\,803\,744\,799\,154], \label{eq:fraiture-first-window}\\
&[105\,000\,001,10^{27}+10^8]. \label{eq:fraiture-large-window} \end{align}"

Encoding: the conjunction of the three per-interval `Prop`s. -/
def Prop_FraitureFinite : Prop :=
  Eq_FraitureSmall ∧ Eq_FraitureFirstWindow ∧ Eq_FraitureLargeWindow

/-- The integers the first verifier check ("small sieve") marks, EP1054.tex lines 746–753:
`N = σ(B) + q ∑_{i=1}^{j} d_i(B)` with `1 ≤ B ≤ 1000`, `q > B` prime, `1 ≤ j ≤ τ(B)`. This is
exactly the existential of `Comp_Verifier_small` (and the form `Step_FraitureSmallBq` represents). -/
def smallSieveMarked (N : ℕ) : Prop :=
  ∃ B q j : ℕ, 1 ≤ B ∧ B ≤ 1000 ∧ q.Prime ∧ B < q ∧ 1 ≤ j ∧ j ≤ B.divisors.card ∧
    N = sig B + q * prefixSumDivisors B j

-- deps: none formal (each conjunct is a finite computation; the second and third are the
--       verifier's check-1 output, with `¬ smallSieveMarked 7` checkable by hand: `B = 1, 2, 3`
--       force `q ∈ {6, 4, 3}`, none admissible, and `B ≥ 4` gives `σ(B) + q > 7`).
-- used by: none (descriptive).
/-- Verifier counts, EP1054.tex lines 839–843 (descriptive reproducibility paragraph, not a paper
environment; **consumed by no proof**). "Specifically, the first check marks $9\,999\,994$ of the
$9\,999\,995$ integers in $[6,10^7]$, with $7$ handled separately; the first prime window contains
$5\,705\,894$ primes; and the large-seed check examines $51\,000\,001$ targets."

Encoding, one conjunct per count:
(1) `[6, 10^7]` has `9 999 995` integers;
(2) exactly `9 999 994` of them satisfy `smallSieveMarked` (the "marks" count, stated as a count,
    not derived from `Comp_Verifier_small`, which only gives the lower bound);
(3) the unmarked one is `7` ("with $7$ handled separately", cf. lines 753–755);
(4) "the first prime window" is the primes of `(M, Y] = (10 000, 99 000 000]`;
(5) the large-seed targets are the integers of `[105 000 000, 156 000 000]` (a pure count: the
    formal content of "examines", with no claim about what the check finds).
The decidability instance for the filter in (2) is classical.

**Not asserted by the spine.** Conjuncts (2) and (4) are a `10^7`-element sieve count and
`π(99·10⁶) − π(10⁴)`: verifier output, not dischargeable under the house rules (`native_decide` is
forbidden), and no proof consumes them. Until 2026-09-25 the spine carried this as a leaf, which
made the whole-paper theorem conditional on an unproved computation; it is now recorded as
descriptive (kind `unasserted` in `spine-dag/dag.py`). -/
def Note_FraitureVerifierCounts : Prop :=
  (Finset.Icc 6 (10 ^ 7)).card = 9999995 ∧
    (haveI := Classical.decPred smallSieveMarked;
      ((Finset.Icc 6 (10 ^ 7)).filter smallSieveMarked).card = 9999994) ∧
    ¬ smallSieveMarked 7 ∧
    ((Finset.Ioc 10000 99000000).filter Nat.Prime).card = 5705894 ∧
    (Finset.Icc 105000000 156000000).card = 51000001

/-! ## Lemma `lem:fraiture-balanced-goldbach` (lines 846–898) -/

-- deps: Cite_Helfgott_weighted (the weighted sum `≥ 0.000422 H²` and the sup norms, with
--       `W = 1.079955² · 1.414`); Cite_RosserSchoenfeld_psi (`ψ(t) ≤ 1.03883 t` at `t = z` and
--       `t = H`: triples with a coordinate `≤ z = H/(30 000 log H)` weigh at most
--       `3Wψ(z)ψ(H) log H < 0.000178 H²`); elementary: triples with a repeated coordinate weigh at
--       most `3WH(log H)³ < 10⁻²⁰ H²` (`(log H)³/H` decreasing, `log 10²⁷ < 63`); so a triple of
--       distinct odd primes all `> z` has nonzero weight. (RS is avoidable: `θ(x) ≤ x log 4`,
--       Mathlib `Chebyshev.theta_le_log4_mul_x`, gives `< 0.00032 H²`; see the Inputs docstring.)
-- used by: Step_FraitureTailEven (line 913), Step_FraitureTailOdd (line 936).
/-- `lem:fraiture-balanced-goldbach`, EP1054.tex line 848.
"Every odd integer $H\geq10^{27}$ is the sum of three distinct odd primes $p,q,r$ satisfying
\[ p,q,r>\frac{H}{30\,000\log H}. \]"

A **paper-proved lemma** (proof lines 856–898), so a proof obligation of the spine: a link from
`Cite_Helfgott_weighted` and `Cite_RosserSchoenfeld_psi`. Until 2026-09-25 this statement was itself
the trusted input `Cite_Helfgott_balanced`, which put the paper's own reduction into the trusted
base under a citation label. -/
def Lem_FraitureBalancedGoldbach : Prop :=
  ∀ H : ℕ, Odd H → 10 ^ 27 ≤ H →
    ∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ Odd p ∧ Odd q ∧ Odd r ∧
      p ≠ q ∧ p ≠ r ∧ q ≠ r ∧ p + q + r = H ∧
      (H : ℝ) / (30000 * Real.log H) < (p : ℝ) ∧
      (H : ℝ) / (30000 * Real.log H) < (q : ℝ) ∧
      (H : ℝ) / (30000 * Real.log H) < (r : ℝ)

/-! ## Proposition `prop:fraiture-tail` (lines 900–953) -/

-- deps: elementary divisor ordering (the divisors of `pqr` below `pq` are `1, p, q, r`).
-- used by: Step_FraitureTailEven.
/-- PROOF STEP of `prop:fraiture-tail`, EP1054.tex lines 920–923 (not a paper environment).
"$pq>\ldots>r$. Hence the divisors of $pqr$ begin with $1,p,q,r$, and their sum is $1+p+q+r$."

Encoding: for primes `p < q < r` with `r < pq`, the prefix `1 + p + q + r` (of `m = pqr`) is
represented. -/
def Step_FraitureTailThreePrimes : Prop :=
  ∀ p q r : ℕ, p.Prime → q.Prime → r.Prime → p < q → q < r → r < p * q →
    1 + p + q + r ∈ R

-- deps: elementary divisor ordering (every product of two of `ℓ < p < q < r` is `≥ ℓp > r`).
-- used by: Step_FraitureTailOdd.
/-- PROOF STEP of `prop:fraiture-tail`, EP1054.tex lines 946–952 (not a paper environment).
"$\ell p>\ldots>r$. Thus the divisors of $\ell pqr$ begin with $1,\ell,p,q,r$, whose sum is
$1+\ell+p+q+r$."

Encoding: for primes `ℓ < p < q < r` with `r < ℓp`, the prefix `1 + ℓ + p + q + r` (of
`m = ℓpqr`) is represented. -/
def Step_FraitureTailFourPrimes : Prop :=
  ∀ l p q r : ℕ, l.Prime → p.Prime → q.Prime → r.Prime → l < p → p < q → q < r → r < l * p →
    1 + l + p + q + r ∈ R

-- deps: Lem_FraitureBalancedGoldbach at `H = n − 1`;
--       Step_FraitureTailThreePrimes; real analysis: `H/(log H)²` increases for `H > e²` and
--       `10^27/(30 000 log 10^27)² > 1`, so `pq > (H/(30 000 log H))² > H > r`.
-- used by: Prop_FraitureTail.
/-- PROOF STEP of `prop:fraiture-tail`, even case, EP1054.tex lines 912–923 (not a paper
environment). "First let $n$ be even and put $H=n-1$. Apply Lemma fraiture-balanced-goldbach, and
order its primes as $p<q<r$. … we have \[ pq>\left(\frac{H}{30\,000\log H}\right)^2>H>r. \]
Hence the divisors of $pqr$ begin with $1,p,q,r$, and their sum is $1+p+q+r=n$." -/
def Step_FraitureTailEven : Prop :=
  ∀ n : ℕ, Even n → 10 ^ 27 + 10 ^ 8 ≤ n → n ∈ R

-- deps: Lem_FraitureBalancedGoldbach at `H = n − 1 − ℓ`;
--       Bertrand (Mathlib `Nat.exists_prime_lt_and_le_two_mul`, strict real form as recorded in
--       the Inputs module docstring) for an odd prime `60 000 log n < ℓ < 120 000 log n`;
--       Step_FraitureTailFourPrimes; real analysis: `h(t) = t − 1 − 120 000 log t − 10^27` has
--       positive derivative on `t ≥ T` and `h(T) > 0` (`log T < 64`), giving `H ≥ 10^27` and
--       `H > n/2`; `n/(log n)²` increases for `n > e²` and exceeds `7.2·10^9` at `n = T`.
-- used by: Prop_FraitureTail.
/-- PROOF STEP of `prop:fraiture-tail`, odd case, EP1054.tex lines 925–952 (not a paper
environment). "Now let $n$ be odd. By Bertrand's postulate, choose an odd prime $\ell$ such that
\[ 60\,000\log n<\ell<120\,000\log n, \] and put $H=n-1-\ell$. … Therefore $H\geq10^{27}$; in the
same way, $H>n/2$. … \[ p>\frac{H}{30\,000\log H}>\frac{n}{60\,000\log n}>120\,000\log n>\ell. \]
… \[ \ell p> 60\,000\log n\cdot\frac{H}{30\,000\log H} >2H>r. \] Thus the divisors of $\ell pqr$
begin with $1,\ell,p,q,r$, whose sum is $1+\ell+p+q+r=n$." -/
def Step_FraitureTailOdd : Prop :=
  ∀ n : ℕ, Odd n → 10 ^ 27 + 10 ^ 8 ≤ n → n ∈ R

-- deps: Step_FraitureTailEven, Step_FraitureTailOdd (hence Lem_FraitureBalancedGoldbach, i.e.
--       Cite_Helfgott_weighted and Cite_RosserSchoenfeld_psi, and Bertrand only — no Comp_*
--       check).
-- used by: Thm_FraitureRepresentability.
/-- `prop:fraiture-tail`, EP1054.tex line 902.
"Every integer \[ n\geq10^{27}+10^8 \] belongs to $\Rcal$." -/
def Prop_FraitureTail : Prop :=
  ∀ n : ℕ, 10 ^ 27 + 10 ^ 8 ≤ n → n ∈ R

/-! ## Theorem `thm:fraiture-representability` (lines 677–684; proof lines 955–966) -/

-- deps: none (elementary: divisors of `1, 2, 3` give `1, 1+2, 1+3`; a prefix is `1`, or
--       `1 + d₂ ≥ 3`, or has length `≥ 3` and sum `≥ 1 + 2 + 3 = 6`; `1 + 4` is impossible since
--       `4 ∣ m ⟹ 2 ∣ m`; and every prefix contains the divisor `1`).
-- used by: Thm_FraitureRepresentability.
/-- PROOF STEP of `thm:fraiture-representability`, EP1054.tex lines 959–965 (not a paper
environment). "The integers $1,3,4$ are represented by $m=1,2,3$, respectively. No prefix can equal
$2$ … a two-term prefix equal to $5$ would have to be $1+4$, but $4\mid m$ implies $2\mid m$,
contradicting that $4$ is the second-smallest divisor. Every prefix of length at least three has
sum at least $1+2+3=6$. Therefore neither $2$ nor $5$ is represented."

Encoding: the three witnesses as `IsRep`; `2 ∉ R`, `5 ∉ R`. The conjunct `0 ∉ R` is **Lean-only**:
the paper's `𝓡` is a set of positive integers by definition (line 98), whereas `Defs.R ⊆ ℕ`, so the
fact that `0` is not a prefix sum must be proved; it is what lets `Thm_FraitureRepresentability`
be a set equality. -/
def Step_FraitureSmallCases : Prop :=
  IsRep 1 1 ∧ IsRep 3 2 ∧ IsRep 4 3 ∧ 2 ∉ R ∧ 5 ∉ R ∧ 0 ∉ R

-- deps: Prop_FraitureFinite (the three intervals overlap: `10^7 ≥ 469 616`,
--       `273 803 744 799 154 ≥ 105 000 001`), Prop_FraitureTail (meets the third interval at
--       `10^27 + 10^8`), Step_FraitureSmallCases.
-- used by: Thm_FraitureRepresentability_Ge6; it IS Eq_ExactRepresentability (S1_Main,
--          eq:exact-representability, line 115), used by prop:tightness-equivalence (line 2695).
/-- `thm:fraiture-representability`, EP1054.tex line 677.
"The represented positive integers are precisely \[ \Rcal=\N\setminus\{2,5\}. \]"

Encoding: the paper's `\N` is the positive integers and its `𝓡` consists of positive integers, so
the statement is the set equality `R = {N | 1 ≤ N ∧ N ≠ 2 ∧ N ≠ 5}` (the `1 ≤ N` conjunct is the
Lean-side `0 ∉ R`, see `Step_FraitureSmallCases`). That set equality is the intro's
`eq:exact-representability` (lines 114–115), stated once as `Eq_ExactRepresentability` in
`S1_Main`; this name is an `abbrev` of it, so the two labels cannot drift apart and a proof of
either is a proof of the other by `id`. -/
abbrev Thm_FraitureRepresentability : Prop := Eq_ExactRepresentability

-- deps: Thm_FraitureRepresentability.
/-- `thm:fraiture-representability`, EP1054.tex line 683, **"in particular" clause**.
"In particular, $f(N)$ is defined for every $N\geq6$."

Encoding: `f` has junk value `0` off `R`, and `N ∈ R` is exactly the condition under which
`f N = sInf {m | 1 ≤ m ∧ IsRep N m}` is a genuine minimiser (`Nat.sInf_mem`); so "`f(N)` is
defined" is `N ∈ R`. -/
def Thm_FraitureRepresentability_Ge6 : Prop :=
  ∀ N : ℕ, 6 ≤ N → N ∈ R

/-! ## The closing remark (lines 969–979) -/

-- deps: the proofs of Thm_FraitureRepresentability, Prop_FraitureTail and
--       Lem_AnalyticOddRepresentability (the three implications below are their spines).
/-- Remark after `thm:fraiture-representability`, EP1054.tex line 971 (unlabelled).
"The exact exceptional set in Theorem fraiture-representability uses the three finite integer
checks in Proposition fraiture-finite. The infinite-tail Proposition fraiture-tail and the analytic
Lemma analytic-odd-representability use none of these checks. In particular, the analytic proofs
of the large-value estimates may use the latter lemma whenever representedness of odd targets is
needed."

Encoding: the remark is a claim about **which inputs each proof consumes**, so it is stated as the
three implications it asserts, with exactly those inputs as hypotheses:
(1) the three verifier checks, Dusart and the balanced-Goldbach inputs (Helfgott's weighted bound
    and Rosser–Schoenfeld) give the theorem;
(2) the tail follows from the balanced-Goldbach inputs alone (no `Comp_*` check);
(3) the analytic lemma follows from Montgomery–Vaughan alone (no `Comp_*` check).
Mathlib facts (Bertrand, Chebyshev's `π(x)` bound, bounds on `e`) are not hypotheses, since they
are proved. That the theorem genuinely *needs* the checks is not a formal claim (it would be a
statement about unprovability) and is not encoded. The last sentence is advisory.

**This `Prop` by itself says nothing** and is not asserted by the spine: each conjunct
`(inputs → X)` follows from `X` alone, whatever `X`'s proof uses. The remark's content is a fact about proofs, and
it lives in the *signature* of `Spine.spine_Rem_FraitureCheckUsage`, which composes the links with
no input in scope except those named here (Lean then checks that each proof uses at most these
inputs), and in `spine-dag/gen.py`, which checks that it uses exactly these. -/
def Rem_FraitureCheckUsage : Prop :=
  (Comp_Verifier_small → Comp_Verifier_window1 → Comp_Verifier_largeSeed →
      Cite_Dusart_Thm69 → Cite_Helfgott_weighted → Cite_RosserSchoenfeld_psi →
      Thm_FraitureRepresentability) ∧
    (Cite_Helfgott_weighted → Cite_RosserSchoenfeld_psi → Prop_FraitureTail) ∧
    (Cite_MV_exceptional → Lem_AnalyticOddRepresentability)

end Principia.Erdos1054
