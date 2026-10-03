/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Erdos1054.Statements.Inputs

set_option autoImplicit false

/-!
# Erdős 1054 (EP1054.tex) — §2 "Arithmetic preliminaries", as statements (lines 350–641)

**Statements only.** Every result of `Campaigns/Erdos-1054/collab-paper/EP1054.tex`, lines 350–641,
is a `def … : Prop` here; nothing is asserted. Proofs come in a later phase, and each `-- deps:`
comment records what that proof consumes (paper results in this or earlier files, and the named
inputs of `Principia.Erdos1054.Statements.Inputs`).

Contents, in paper order:

* line 360 — `Disp_FinalDivisor` (`F_e(d) ≥ d`, `F_e(d) ≤ X ⟹ ed ≤ eX`);
* lines 362–368 — the Mertens/Chebyshev display: **inputs only**, see the section note below;
* lines 372–377 — `Eq_Reflection` (`eq:reflection`);
* lines 383–405 — the forced-modulus preamble: `Fact_KmodGeTwo`, `Dperiod`, `Fact_DsetResidue`,
  `Fact_KmodFinite`;
* lines 406–440 — `Lem_FmModulus` = `Eq_FmReflection` ∧ `Lem_FmModulus_Divides` ∧
  `Eq_FmCongruence` ∧ `Lem_FmModulus_Maximal`;
* lines 441–448 — `Rem_RoughInputModulus` (`K_{e,d} = σ(e) − 1` when `P^-(d) ≥ e`);
* lines 452–459 — `Lem_FixedModulusNormality`;
* lines 484–487 — `Lem_SigmaRangeZero`;
* lines 500–519 — `Bq`, `hq` (proof-local), `Lem_SigmaRate` = `Lem_SigmaRate_OddPrime` ∧
  `Lem_SigmaRate_B2`;
* lines 565–581 — `zetaR`, `momentConst` (proof-local), `momentSum`, `largeCofactorSet`,
  `Lem_Moment` built from `Eq_CkGrowth`, `Eq_Moment`, `Eq_LargeCount`.

The objects `F`, `g`, `sig`, `Dset`, `Mlcm`, `Csum`, `Kmod`, `cnt`, `DensZero`, `logIt` are those of
`Principia.Erdos1054.Defs`; the paper's `g = gcd(e, M)` of line 390 is written out as
`Nat.gcd e (Mlcm e d)` (the name `g` is taken by the reciprocal sum `g_e(n)`).
-/

namespace Principia.Erdos1054

open Finset Filter
open scoped Topology

/-! ## The displayed facts after the notation (lines 353–368) -/

-- deps: none (definition of `F`: `d ∣ e d` and `d ≤ d`, so `d` is a summand of `F e d`; then
--       `e d ≤ e F_e(d) ≤ e X`). The first conjunct is `Principia.Erdos1054.F_ge` (Basic.lean).
/-- **Display after the definition of `g_e`**, EP1054.tex lines 358–361 (unlabeled).
"Since the final divisor occurs in its own prefix,
`\[ F_e(d)\geq d,\quad F_e(d)\leq X\ \Longrightarrow\ ed\leq eX. \]`"

Encoding: `e, d ≥ 1` (the paper's cofactor setting; `e ≥ 1` is needed, since `F 0 d = 0` because
`Nat.divisors 0 = ∅`). `X` is real and `ed ≤ eX` is read in `ℝ`, `X` being an arbitrary real
threshold as in the counting arguments that use it. -/
def Disp_FinalDivisor : Prop :=
  ∀ e d : ℕ, 1 ≤ e → 1 ≤ d →
    d ≤ F e d ∧ ∀ X : ℝ, (F e d : ℝ) ≤ X → (e : ℝ) * d ≤ e * X

/-! ### The Mertens/Chebyshev display (lines 362–368) — inputs, not restated

"Mertens' theorem and Chebyshev's estimates give
`\[ \Delta(y)\sim\frac{e^{-\gamma}}{\log y}, \quad \log(y\#)\ll y,
\quad \log\Lambda(u)=\psi(u)\leq C_\Lambda u; \]` see, for example, \cite{Tenenbaum}."

* `Δ(y) ∼ e^{-γ}/log y` is the input `Std_Mertens3` (`Delta y * log y → exp (−γ)`).
* `log(y#) ≪ y` is in the pinned Mathlib: `Chebyshev.theta_eq_log_primorial`
  (`θ x = log (primorial ⌊x⌋₊)`, and `primorialR y = primorial ⌊y⌋₊` by definition) with
  `Chebyshev.theta_le_log4_mul_x`, or directly `primorial_le_four_pow`.
* `log Λ(u) = ψ(u) ≤ C_Λ u` (for real `u ≥ 1`, line 322) is in the pinned Mathlib:
  `Chebyshev.psi_eq_psi_coe_floor` (`ψ u = ψ ⌊u⌋₊`) with `Chebyshev.psi_eq_log_lcmUpto`
  (`ψ n = log (Nat.lcmUpto n)` at a natural `n`; `lcmUpTo u` has the same body as
  `Nat.lcmUpto ⌊u⌋₊`) and `Chebyshev.psi_le_const_mul_self` (`0 ≤ x → ψ x ≤ (log 4 + 4) x`), so
  `C_Λ = log 4 + 4`. The floor step is needed: `psi_eq_log_lcmUpto` alone is only for natural
  arguments.

**Why no `Prop` is made here.** The facts are used later — `P# = exp(O(P))` (line 2129) and
`log Λ(F) ≪ F`, `log(P#) ≪ P` (lines 2189–2190) in the proof of thm:subexp-growth, and
`log Λ(A) = ψ(A)` at line 2532 — so the reason is not that they are unused. It is the policy of
`Statements/Inputs.lean` ("Pinned-Mathlib audit"): an outside input already in the pinned
Mathlib is not restated, and its consumers cite the Mathlib names above directly in their
`-- deps:` (as S1_Main, S4b_SmallValues, S5_UpperTails and S6_Coverage do). The Mertens half is
not in Mathlib, which is why it alone is a named input. -/

/-! ## The reflection lemma (lines 370–381) -/

-- deps: none (the divisor involution `r ↦ ed/r`, Mathlib `Nat.sum_div_divisors`).
--       Already PROVED as `Principia.Erdos1054.reflection` (Basic.lean), same statement shape.
/-- **Lemma (reflection), `eq:reflection`**, EP1054.tex lines 372–377.
"`\begin{lemma} For every $e,d\geq1$, \begin{equation}\label{eq:reflection}
F_e(d)=ed\,g_e(ed). \end{equation} \end{lemma}`"

Encoding: stated in `ℝ` (`g` is real-valued), with `ed` cast as `(e : ℝ) * d`, exactly the shape
of `Principia.Erdos1054.reflection`, so the later proof of this `Prop` is that theorem. -/
def Eq_Reflection : Prop :=
  ∀ e d : ℕ, 1 ≤ e → 1 ≤ d → (F e d : ℝ) = (e * d : ℝ) * g e (e * d)

/-! ## The exact forced modulus: preamble (lines 383–405)

"Fix `e ≥ 2` and `d ≥ 1`, put `n = ed`, and let `D = {j : 1 ≤ j < e, j ∣ n}` … Put
`M = lcm(D)`, `C = ∑_{j∈D} M/j`, `g = gcd(e, M)`, `K_{e,d} = (e/g) C`." These are `Dset`, `Mlcm`,
`Csum`, `Kmod` of `Defs`; all divisions in `Csum`/`Kmod` are exact (`j ∣ M`, `gcd ∣ e`). -/

-- deps: none (`1 ∈ D` since `e ≥ 2`; `C ≥ M/1 = M`; `e/g = 1 ⟹ e ∣ M ⟹ M ≥ e`).
/-- **Positivity of the modulus data and `K_{e,d} ≥ 2`**, EP1054.tex line 393 (unlabeled).
"Since `$1\in D$`, these are positive integers. In fact `$K_{e,d}\geq2$`: if `$e/g>1$` this is
immediate, while `$e/g=1$` implies `$C\geq M\geq e\geq2$`."

Encoding: `g = Nat.gcd e (Mlcm e d)`; `e/g` is `Nat` division (exact, `g ∣ e`). The chain
`C ≥ M ≥ e` in the case `e/g = 1` is recorded because a later proof reuses it
(cor:fm-envelope-tail, line 2047: "Now `C ≥ M ≥ e ≥ 2`"). -/
def Fact_KmodGeTwo : Prop :=
  ∀ e d : ℕ, 2 ≤ e → 1 ≤ d →
    1 ∈ Dset e d ∧ 0 < Mlcm e d ∧ 0 < Csum e d ∧ 2 ≤ Kmod e d ∧
      (e / Nat.gcd e (Mlcm e d) = 1 → e ≤ Mlcm e d ∧ Mlcm e d ≤ Csum e d)

/-- The period `lcm({j / gcd(j, e) : 1 ≤ j < e})` of `d ↦ D` (EP1054.tex lines 401–403).
Section-local object. `Nat` division is exact (`gcd(j, e) ∣ j`). -/
def Dperiod (e : ℕ) : ℕ := (Finset.Ico 1 e).lcm (fun j => j / Nat.gcd j e)

-- deps: none (`j/h` and `e/h` are coprime for `h = gcd(j, e)`: Mathlib `Nat.coprime_div_gcd_div_gcd`,
--       `Nat.Coprime.dvd_of_dvd_mul_left`; then `j/h ∣ Dperiod e`).
/-- **`D` depends only on `d` modulo `Dperiod e`**, EP1054.tex lines 393–403 (unlabeled).
"For `$1\leq j<e$` write `$h=\gcd(j,e)$`. Then
`\[ j\mid ed\quad\Longleftrightarrow\quad \frac jh\mid\frac eh\,d
\quad\Longleftrightarrow\quad \frac jh\mid d, \]` because `$j/h$` and `$e/h$` are coprime. Thus
`$D$` depends only on the residue of `$d$` modulo
`\[ \lcm\bigl(\{j/\gcd(j,e):1\leq j<e\}\bigr). \]`"

Encoding: the outer equivalence `j ∣ e d ↔ j/h ∣ d` (the middle term is proof), and the
periodicity as `d ≡ d' [MOD Dperiod e] → Dset e d = Dset e d'` for `d, d' ≥ 1`. -/
def Fact_DsetResidue : Prop :=
  ∀ e : ℕ, 2 ≤ e →
    (∀ j d : ℕ, 1 ≤ j → j < e → (j ∣ e * d ↔ j / Nat.gcd j e ∣ d)) ∧
    (∀ d d' : ℕ, 1 ≤ d → 1 ≤ d' → d ≡ d' [MOD Dperiod e] → Dset e d = Dset e d')

-- deps: Fact_DsetResidue (or directly: `Kmod e d` is a function of `Dset e d ⊆ Ico 1 e`).
/-- **`K_{e,d}` takes finitely many values for fixed `e`**, EP1054.tex lines 404–405 (unlabeled).
"In particular, for fixed `$e$` the integer `$K_{e,d}$` takes only finitely many values."
(Reused by prop:fm-envelope, line 2516: "There are only finitely many such moduli.") -/
def Fact_KmodFinite : Prop :=
  ∀ e : ℕ, 2 ≤ e → {K : ℕ | ∃ d : ℕ, 1 ≤ d ∧ Kmod e d = K}.Finite

/-! ## `lem:fm-modulus` (lines 406–440) -/

-- deps: none — no paper result or input (lines 419–426). The divisor involution `r ↦ n/r` of
--       `n.divisors` (`n = e d`), with `r > d ⟺ n/r < e`, gives
--       `σ(n) − F_e(d) = ∑_{r ∣ n, r > d} r = ∑_{j ∈ D} n/j = (n/M) C`; `M ∣ n` because every
--       `j ∈ D` divides `n` (Mathlib `Finset.lcm_dvd`). Setting `e ≥ 2, d ≥ 1` from Lem_FmModulus.
/-- **`eq:fm-reflection`**, EP1054.tex lines 408–410: `F_e(d)=\sigma(n)-\frac nM\,C` with
`n = ed`.

Encoding: the proof's integrality claim "`M ∣ n` and `n/M` is an integer" (line 425) is the first
conjunct, so the `Nat` division `e * d / Mlcm e d` is exact; the identity is stated additively in
`ℕ`, `F + (n/M) C = σ(n)`, which avoids truncated subtraction and is equivalent to the display
over `ℤ`. -/
def Eq_FmReflection (e d : ℕ) : Prop :=
  Mlcm e d ∣ e * d ∧ F e d + (e * d / Mlcm e d) * Csum e d = sig (e * d)

-- deps: Eq_FmReflection e d (its first conjunct, `M ∣ e d`; lines 427–428). Then `M/g` and `e/g`
--       are coprime for `g = gcd(e, M) > 0` (`Nat.coprime_div_gcd_div_gcd`), `M/g ∣ (e/g) d`, and
--       `Nat.Coprime.dvd_of_dvd_mul_left` gives `M/g ∣ d`.
/-- **`lem:fm-modulus`, middle clause**, EP1054.tex line 411: "the integer `$M/g$` divides `$d$`".
`M/g` is `Nat` division, exact since `gcd(e, M) ∣ M`. -/
def Lem_FmModulus_Divides (e d : ℕ) : Prop :=
  Mlcm e d / Nat.gcd e (Mlcm e d) ∣ d

-- deps: Eq_FmReflection e d and Lem_FmModulus_Divides e d (lines 429–433):
--       `n/M = (e/g)·(d/(M/g))`, so `σ(n) − F_e(d) = (n/M) C` is a multiple of `(e/g) C = K_{e,d}`;
--       then Mathlib `Nat.modEq_iff_dvd'` (`F_e(d) ≤ σ(n)`).
/-- **`eq:fm-congruence`**, EP1054.tex lines 412–414: `F_e(d)\equiv\sigma(n)\pmod{K_{e,d}}`. -/
def Eq_FmCongruence (e d : ℕ) : Prop :=
  F e d ≡ sig (e * d) [MOD Kmod e d]

-- deps: (i) Eq_FmCongruence e d' for each `d'` in the class, with `Kmod e d' = Kmod e d`
--       (`Kmod` is a function of `Dset` alone: unfold `Kmod`, `Csum`, `Mlcm`).
--       (ii) the witness `d₀ = M/g` (lines 434–439): `d₀ ≥ 1` from Fact_KmodGeTwo (`0 < M`) and
--       `g ∣ M`; `Dset e d₀ = Dset e d` from `j ∣ M ∣ e d₀ = lcm(e, M)` and, conversely,
--       `e d₀ ∣ e d` by Lem_FmModulus_Divides e d; then Eq_FmReflection e d₀ makes the difference
--       at `d₀` exactly `(e d₀/M) C = (e/g) C = K_{e,d}`, and Mathlib `Nat.modEq_iff_dvd'` turns
--       validity of `K` at `d₀` into `K ∣ K_{e,d}`.
/-- **`lem:fm-modulus`, maximality clause**, EP1054.tex lines 415–416: "Moreover `$K_{e,d}$` is the
largest modulus for which `\eqref{eq:fm-congruence}` holds for every `$d$` with the same set `$D$`."

Encoding: (i) `K_{e,d}` is valid for the whole class `{d' ≥ 1 : Dset e d' = Dset e d}`, and
(ii) every modulus `K` valid for that class divides `K_{e,d}`. The paper says "largest"; its proof
(lines 438–439: "Any modulus valid for every `d` with this set `D` divides that difference, hence
divides `K_{e,d}`") establishes divisibility, which is what is stated; since `K_{e,d} ≥ 2 > 0`
(`Fact_KmodGeTwo`) divisibility implies `K ≤ K_{e,d}`. A modulus `K = 0` means equality, which is
never valid (`σ(n) − F_e(d) = (n/M) C > 0`), so (ii) does not need `K ≥ 1`. -/
def Lem_FmModulus_Maximal (e d : ℕ) : Prop :=
  (∀ d' : ℕ, 1 ≤ d' → Dset e d' = Dset e d → F e d' ≡ sig (e * d') [MOD Kmod e d]) ∧
  ∀ K : ℕ, (∀ d' : ℕ, 1 ≤ d' → Dset e d' = Dset e d → F e d' ≡ sig (e * d') [MOD K]) →
    K ∣ Kmod e d

-- deps: its four clauses, in the chain recorded on each: Eq_FmReflection (no paper result) →
--       Lem_FmModulus_Divides → Eq_FmCongruence → Lem_FmModulus_Maximal (which also uses
--       Eq_FmReflection at `d₀ = M/g` and Fact_KmodGeTwo for `d₀ ≥ 1`). No input, and no paper
--       result outside this section.
/-- **Lemma `lem:fm-modulus`**, EP1054.tex lines 406–417.
"`\begin{lemma}\label{lem:fm-modulus} With the notation above,
\begin{equation}\label{eq:fm-reflection} F_e(d)=\sigma(n)-\frac nM\,C , \end{equation}
the integer $M/g$ divides $d$, and \begin{equation}\label{eq:fm-congruence}
F_e(d)\equiv\sigma(n)\pmod{K_{e,d}} . \end{equation} Moreover $K_{e,d}$ is the largest modulus
for which \eqref{eq:fm-congruence} holds for every $d$ with the same set $D$. \end{lemma}`"

"The notation above" (line 384): `e ≥ 2`, `d ≥ 1`, `n = e d`. -/
def Lem_FmModulus : Prop :=
  ∀ e d : ℕ, 2 ≤ e → 1 ≤ d →
    Eq_FmReflection e d ∧ Lem_FmModulus_Divides e d ∧ Eq_FmCongruence e d ∧
      Lem_FmModulus_Maximal e d

/-! ## The rough-input remark (lines 441–448) -/

-- deps: Fact_DsetResidue (the criterion `j ∣ ed ↔ j/gcd(j,e) ∣ d`, and `j/gcd(j,e) ≤ j < e ≤ P^-(d)`
--       forces `j/gcd(j,e) = 1`), Lem_FmModulus (Eq_FmCongruence), and
--       `∑_{j ∣ e, j < e} e/j = σ(e) − 1` (divisor involution, Mathlib `Nat.sum_div_divisors`).
/-- **Remark: the modulus on rough inputs**, EP1054.tex lines 441–448 (unlabeled).
"If `$P^-(d)\geq e$`, then `$D$` is the set of divisors of `$e$` below `$e$`. Indeed, for `$j<e$`
the integer `$j/\gcd(j,e)$` is below `$e\leq P^-(d)$`, so it divides `$d$` only if it equals `$1$`,
that is, only if `$j\mid e$`. In this case `$M\mid e$`, `$g=M$`, and
`\[ K_{e,d}=\sum_{\substack{j\mid e\\ j<e}}\frac ej=\sigma(e)-1 . \]` So on `$e$`-rough inputs,
`$F_e(d)\equiv\sigma(ed)\pmod{\sigma(e)-1}$`."

Encoding: `P^-(d) ≥ e` is `∀ p ∈ d.primeFactors, e ≤ p` (vacuous for `d = 1`, matching
`P^-(1) = ∞`). The paper's closing sentence says "`e`-rough" (`P^-(d) > e`, line 317), which is a
special case of the hypothesis actually used, `P^-(d) ≥ e`; the weaker hypothesis is kept.
"The set of divisors of `e` below `e`" is Mathlib's `e.properDivisors` (`{j ∈ Ico 1 e | j ∣ e}`).
`σ(e) − 1` is truncated `Nat` subtraction, harmless since `σ(e) ≥ e + 1 ≥ 3`. The setting
`e ≥ 2, d ≥ 1` is that of `lem:fm-modulus`. -/
def Rem_RoughInputModulus : Prop :=
  ∀ e d : ℕ, 2 ≤ e → 1 ≤ d → (∀ p ∈ d.primeFactors, e ≤ p) →
    Dset e d = e.properDivisors ∧ Mlcm e d ∣ e ∧ Nat.gcd e (Mlcm e d) = Mlcm e d ∧
      Kmod e d = ∑ j ∈ e.properDivisors, e / j ∧ Kmod e d = sig e - 1 ∧
      F e d ≡ sig (e * d) [MOD sig e - 1]

/-! ## `lem:fixed-modulus-normality` and `lem:sigma-range-zero` (lines 450–498) -/

-- deps: Std_recipPrimesAP_diverges (primes `≡ −1 (mod q)`, `q` a prime power); the Chinese
--       remainder theorem (Mathlib `Nat.chineseRemainder`) for the density of
--       `{n : r ∤∥ n for all r ∈ 𝒫}`; `σ` multiplicative with `σ(r) = r + 1`; the union bound over
--       the prime-power factors of `V`; `∏ (1 − 1/r + 1/r²) → 0` from the divergence.
/-- **Lemma `lem:fixed-modulus-normality`**, EP1054.tex lines 452–459.
"`\begin{lemma} \label{lem:fixed-modulus-normality} For every fixed positive integer $V$,
\[ \#\{n\leq Y:V\nmid\sigma(n)\}=o_V(Y) \quad(Y\to\infty). \] \end{lemma}`"

Encoding: `DensZero` (`cnt S X / X → 0` along the integers; equivalent to `o(Y)` along the reals
since `cnt S Y = cnt S ⌊Y⌋` and `⌊Y⌋ ≤ Y`). `n` ranges over `n ≥ 1` (`cnt` starts at `1`). The
`o_V` dependence is carried by the order `∀ V, DensZero …`. -/
def Lem_FixedModulusNormality : Prop :=
  ∀ V : ℕ, 1 ≤ V → DensZero {n : ℕ | ¬ V ∣ sig n}

-- deps: Lem_FixedModulusNormality; `σ(n) ≥ n` (so `σ(n) ≤ X ⟹ n ≤ X`), the count of multiples of
--       `q` up to `X`, and `q → ∞`.
/-- **Lemma `lem:sigma-range-zero`**, EP1054.tex lines 484–487.
"`\begin{lemma} \label{lem:sigma-range-zero} The set $\sigma(\N)=\{\sigma(n):n\geq1\}$ has
asymptotic density zero. \end{lemma}`"

Encoding: `σ(ℕ) = {N | ∃ n ≥ 1, σ(n) = N}` (Mathlib's `σ 1 0 = 0` is excluded by `n ≥ 1`, and
`cnt` counts from `1` anyway). -/
def Lem_SigmaRangeZero : Prop :=
  DensZero {N : ℕ | ∃ n : ℕ, 1 ≤ n ∧ sig n = N}

/-! ## `lem:sigma-rate` (lines 500–560) -/

/-- `B_q(y) = #{n ≤ y : q ∤ σ(n)}`, EP1054.tex lines 500–503 ("For a prime `$q$` and a real number
`$y\geq1$`, define `\[ B_q(y)=\#\{n\leq y:q\nmid\sigma(n)\}. \]`"). Section-local object; `n ≥ 1`. -/
noncomputable def Bq (q : ℕ) (y : ℝ) : ℕ := cnt {n : ℕ | ¬ q ∣ sig n} y

open Classical in
/-- **Proof-local object** `h_q` of `lem:sigma-rate`, EP1054.tex lines 522–529:
"`h_q(p^\nu):= 0` if `p\equiv-1\pmod q` and `\nu=1`, `1` otherwise", extended multiplicatively.
Closed form used here: `h_q(n) = 0` if some prime `p ≡ −1 (mod q)` (i.e. `q ∣ p + 1`) exactly
divides `n` (`v_p(n) = 1`), and `1` otherwise (`h_q(0) = 0`). That this is multiplicative, with the
stated prime-power values, is a proof obligation of the proof phase (needed to apply
`Cite_Pollack_Lemma24`); it is not a paper result. -/
noncomputable def hq (q : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 0 then 0 else
      if ∃ p ∈ n.primeFactors, q ∣ p + 1 ∧ n.factorization p = 1 then 0 else 1,
    by simp⟩

-- deps: Cite_Pollack_Lemma24 applied to `hq q` (multiplicative, values in `[0, 1]`, and
--       `1_{q ∤ σ(n)} ≤ h_q(n)` because `p ≡ −1 (q)`, `v_p(n) = 1` give `q ∣ σ(p) ∣ σ(n)`;
--       lines 522–540); Std_SiegelWalfisz_dyadic summed over dyadic intervals from
--       `z = exp(C q²)` to `y` (lines 543–557; `z ≤ y` from the range of `q` after shrinking `c₀`).
--       No earlier paper result.
/-- **`lem:sigma-rate`, first assertion** (odd primes), EP1054.tex lines 508–517.
"There are absolute constants `$c_0,c_1>0$` such that, for all sufficiently large `$y$` and every
prime `\[ 3\leq q\leq c_0\frac{\log\log y}{\log\log\log y}, \]` one has
`\[ B_q(y)\ll y\exp\!\left(-c_1\frac{\log\log y}q\right). \]`"

Encoding: `∃ c₀ > 0, ∃ c₁ > 0, ∃ C, ∃ y₀, ∀ y ≥ y₀, ∀ prime q` in the range,
`B_q(y) ≤ C y exp(−c₁ log log y / q)`. The implied constant `C` is absolute (line 336: "All implied
constants are absolute unless their dependence is indicated"), so it precedes `y` and `q`;
`log log = logIt 2`, `log log log = logIt 3`. -/
def Lem_SigmaRate_OddPrime : Prop :=
  ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ C : ℝ, ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y →
    ∀ q : ℕ, q.Prime → 3 ≤ q → (q : ℝ) ≤ c₀ * logIt 2 y / logIt 3 y →
      (Bq q y : ℝ) ≤ C * y * Real.exp (-(c₁ * logIt 2 y / q))

-- deps: Std_sigma_odd_iff (lines 558–559), so `B_2(y) ≤ #{m ≥ 1 : m² ≤ y} + #{m ≥ 1 : 2m² ≤ y}
--       ≤ 2√y`. No earlier paper result.
/-- **`lem:sigma-rate`, second assertion**, EP1054.tex line 518: "Also `$B_2(y)\ll\sqrt y$`."

Encoding: `∃ C, ∀ y ≥ 1, B_2(y) ≤ C √y` (`B_q` is defined for real `y ≥ 1`, line 500; the
implied constant is absolute). -/
def Lem_SigmaRate_B2 : Prop :=
  ∃ C : ℝ, ∀ y : ℝ, 1 ≤ y → (Bq 2 y : ℝ) ≤ C * Real.sqrt y

-- deps: its two clauses: Lem_SigmaRate_OddPrime (Cite_Pollack_Lemma24 applied to `hq q`,
--       Std_SiegelWalfisz_dyadic) and Lem_SigmaRate_B2 (Std_sigma_odd_iff). No earlier paper result.
/-- **Lemma `lem:sigma-rate`**, EP1054.tex lines 508–519.
"`\begin{lemma}\label{lem:sigma-rate} There are absolute constants $c_0,c_1>0$ such that, for all
sufficiently large $y$ and every prime \[ 3\leq q\leq c_0\frac{\log\log y}{\log\log\log y}, \]
one has \[ B_q(y)\ll y\exp\!\left(-c_1\frac{\log\log y}q\right). \] Also $B_2(y)\ll\sqrt y$.
\end{lemma}`" -/
def Lem_SigmaRate : Prop :=
  Lem_SigmaRate_OddPrime ∧ Lem_SigmaRate_B2

/-! ## `lem:moment` (lines 562–638) -/

/-- The real Dirichlet series `ζ(s) = ∑_{n ≥ 1} n^{-s}` (for `s > 1`), in the summand form of the
Mathlib-derived bound `ζ(1 + u) ≤ 1 + 1/u` (see the `Statements.Inputs` header; formerly the input
`Std_zeta_le`). Proof-local helper for `momentConst`. -/
noncomputable def zetaR (s : ℝ) : ℝ := ∑' n : ℕ, (((n : ℝ) + 1) ^ s)⁻¹

/-- **The paper's constant** `C_k := ∏_{j=1}^{k+1} ζ(1 + j/(k+1))^{\binom{k+1}{j}}`, EP1054.tex
lines 619–623. The lemma asserts only the *existence* of a constant (`Lem_Moment`), and the Lean
proof (`Proofs/Moment.lean`, `link_Lem_Moment`) does **not** use this one: its witness is
`C_k = (k+2)^{2^{k+1}}`, the bound the paper's own proof of `eq:Ck-growth` puts on this product
(each of the `2^{k+1} − 1` zeta factors is at most `k + 2`). No statement mentions `momentConst`;
it is kept as the paper's reference value. -/
noncomputable def momentConst (k : ℕ) : ℝ :=
  ∏ j ∈ Finset.Icc 1 (k + 1), zetaR (1 + (j : ℝ) / ((k : ℝ) + 1)) ^ ((k + 1).choose j)

/-- The moment sum `∑_{n ≤ Z} ∑_{e ∣ n, e > E} g_e(n)^k` of `eq:moment` (`n ≥ 1`, `E, Z` real). -/
noncomputable def momentSum (k : ℕ) (E Z : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊Z⌋₊, ∑ e ∈ n.divisors.filter (fun e : ℕ => E < (e : ℝ)), g e n ^ k

/-- The set counted in `eq:large-count`: the `N` "for which there are `$e,d\in\N$` satisfying
`$N=F_e(d)$`, `$e>E$`, and `$ed\leq AN$`" (EP1054.tex lines 575–577). `ℕ` is `{1, 2, …}` in the paper,
so `e, d ≥ 1`; `A, E` real. -/
def largeCofactorSet (A E : ℝ) : Set ℕ :=
  {N : ℕ | ∃ e d : ℕ, 1 ≤ e ∧ 1 ≤ d ∧ N = F e d ∧ E < (e : ℝ) ∧ (e * d : ℝ) ≤ A * N}

-- deps: Mathlib `ZetaAsymptotics.zeta_limit_aux1` + `ZetaAsymptotics.term_nonneg` (`ζ(1 + u) ≤
--       1 + 1/u`, lines 625–627; this replaced the former input `Std_zeta_le`, removed from
--       Inputs on 2026-09-25):
--       `ζ(1 + j/(k+1)) ≤ 1 + (k+1)/j ≤ k + 2 ≤ 2k + 2`, and
--       `∑_{j=1}^{k+1} binom(k+1, j) ≤ 2^{k+1}` (Mathlib `Nat.sum_range_choose`); `0 < C_k` from
--       each `ζ` value being a positive summable tsum (Mathlib `Real.summable_one_div_nat_rpow`).
--       That is the paper's route for its `C_k = momentConst k`. The Lean proof
--       (`Proofs/Moment.lean`, `Moment.ck_growth`) proves it for the witness
--       `Ck = (k+2)^{2^{k+1}}` instead: `log C_k = 2^{k+1} log(k+2) ≤ 2^{k+1} log(2k+2)`, with no
--       zeta value (the ζ bound is spent in `eq:moment`). No paper result.
/-- **`eq:Ck-growth`**, EP1054.tex lines 567–569: `\log C_k\leq 2^{k+1}\log(2k+2)`.

Encoding: `0 < C_k` is made explicit — `log C_k` is only meaningful for `C_k > 0` (Mathlib's
`Real.log` is `log |x|` and `log 0 = 0`), and the paper's `C_k` is a product of zeta values `> 1`. -/
def Eq_CkGrowth (k : ℕ) (Ck : ℝ) : Prop :=
  0 < Ck ∧ Real.log Ck ≤ (2 : ℝ) ^ (k + 1) * Real.log (2 * (k : ℝ) + 2)

-- deps: none — no paper result or input (lines 584–625). Expanding the `k`-th power and counting
--       common multiples, `⌊Z/lcm⌋ ≤ Z/lcm`, `R^{1/(k+1)}/(r₁⋯r_k) ≤ e^{1−k} ≤ E^{1−k}`, the `y_S`
--       factorisation of `(x₀,…,x_k)` (`R = ∏ y_S^{|S|}`, `lcm = ∏ y_S`), and summability of
--       `∑_y y^{-1-|S|/(k+1)}` (Mathlib `Real.summable_one_div_nat_rpow`). Proved
--       (`Proofs/Moment.lean`, `Moment.moment_bound`) for the witness `Ck = (k+2)^{2^{k+1}}`, not
--       `momentConst k`: each factor `∑_{y ≤ N} y^{-1-|S|/(k+1)}` is bounded by `1 + (k+1)/|S| ≤
--       k + 2` on finite partial sums (`Moment.partial_zeta_le`, from Mathlib's
--       `ZetaAsymptotics.zeta_limit_aux1`), and there are `2^{k+1}` subsets `S`.
/-- **`eq:moment`**, EP1054.tex lines 570–574: "for all `$E,Z\geq1$`,
`\sum_{n\leq Z}\ \sum_{\substack{e\mid n\\e>E}}g_e(n)^k \leq C_kZE^{1-k}`."

Encoding: `E, Z` real (the paper does not restrict `E` to integers; its proof uses only
`e > E ⟹ e^{1-k} ≤ E^{1-k}`); `E^{1-k}` is `Real.rpow` with exponent `1 − (k : ℝ)`. -/
def Eq_Moment (k : ℕ) (Ck : ℝ) : Prop :=
  ∀ E Z : ℝ, 1 ≤ E → 1 ≤ Z → momentSum k E Z ≤ Ck * Z * E ^ (1 - (k : ℝ))

-- deps: Eq_Reflection (`N = F_e(d) = n g_e(n)` with `n = e d`, so `n ≤ A X` and
--       `g_e(n) = N/n ≥ 1/A`); Eq_Moment k Ck at `Z = A X` (`≥ 1`); Markov's inequality
--       (`1 ≤ (A g_e(n))^k` on the counted pairs); the pair `(e, n)` determines `N = F_e(n/e)`, so
--       distinct `N` give distinct pairs (lines 629–637). The link
--       `Eq_Reflection → Eq_Moment k Ck → Eq_LargeCount k Ck` holds for every `k` and every `Ck`.
/-- **`eq:large-count`**, EP1054.tex lines 575–580: "Consequently, for all real `$A,X\geq1$`, the
number of integers `$N\leq X$` for which there are `$e,d\in\N$` satisfying `$N=F_e(d)$`, `$e>E$`, and
`$ed\leq AN$` is at most `C_kA^{k+1}E^{1-k}X`."

Encoding: `cnt (largeCofactorSet A E) X` (counts `1 ≤ N ≤ ⌊X⌋`; `N = F_e(d) ≥ d ≥ 1` anyway);
`E ≥ 1` real, inherited from the lemma's "for all `E,Z ≥ 1`"; the same `C_k` as in `eq:moment`. -/
def Eq_LargeCount (k : ℕ) (Ck : ℝ) : Prop :=
  ∀ A X E : ℝ, 1 ≤ A → 1 ≤ X → 1 ≤ E →
    (cnt (largeCofactorSet A E) X : ℝ) ≤ Ck * A ^ (k + 1) * E ^ (1 - (k : ℝ)) * X

-- deps: its three clauses at one witness `Ck`: Eq_CkGrowth, Eq_Moment (no paper result or input),
--       Eq_LargeCount (Eq_Reflection and Eq_Moment k Ck). The paper's witness is
--       `momentConst k`; the Lean proof (`Proofs/Moment.lean`, `link_Lem_Moment`) uses
--       `Ck = (k+2)^{2^{k+1}}`, which bounds it factor by factor.
--       Consumers that count witnessing *pairs* rather than values (e.g. lines 2815–2823) use
--       Eq_Moment with Eq_Reflection directly, not Eq_LargeCount.
/-- **Lemma `lem:moment`**, EP1054.tex lines 565–581.
"`\begin{lemma}\label{lem:moment} For every integer $k\geq2$ there is a constant $C_k$ satisfying
\begin{equation}\label{eq:Ck-growth} \log C_k\leq 2^{k+1}\log(2k+2) \end{equation} such that, for
all $E,Z\geq1$, \begin{equation}\label{eq:moment} \sum_{n\leq Z}\ \sum_{\substack{e\mid n\\e>E}}
g_e(n)^k \leq C_kZE^{1-k}. \end{equation} Consequently, for all real $A,X\geq1$, the number of
integers $N\leq X$ for which there are $e,d\in\N$ satisfying $N=F_e(d)$, $e>E$, and $ed\leq AN$ is
at most \begin{equation}\label{eq:large-count} C_kA^{k+1}E^{1-k}X. \end{equation} \end{lemma}`"

Encoding: one constant `C_k` serves all three displays (`∃ Ck` scopes over the conjunction); it
depends on `k` only, and is uniform in `E, Z, A, X`. -/
def Lem_Moment : Prop :=
  ∀ k : ℕ, 2 ≤ k → ∃ Ck : ℝ, Eq_CkGrowth k Ck ∧ Eq_Moment k Ck ∧ Eq_LargeCount k Ck

end Principia.Erdos1054
