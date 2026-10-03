/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Erdos1054.Defs
import Principia.Erdos1054.Statements.S1_Main
import Mathlib.Data.Fintype.Pi

set_option autoImplicit false

/-!
# Erdős 1054 (EP1054.tex) — §4, part 1: small values of `f(N)/N` (lines 983–1303)

**Statements only.** Every paper claim in lines 983–1303 is a `def … : Prop`; nothing is asserted.
The spine composes these as named hypotheses.

`Statements.Inputs` is deliberately **not imported**: its names (`Std_Mertens2`, `Cite_Axler_Cor2`,
`Std_primes_dyadic_lower`, `Std_totient_sigma`) occur here only in `-- deps:` comments and
docstrings, no def body uses it, and importing it would only couple this module's rebuilds to its
measure-theory imports. The spine imports `Inputs` directly. `Statements.S1_Main` **is** imported:
the proof steps of Theorem 1.1 below count `smallRatioSet δ`, the set Theorem 1.1 is stated about.

Contents, in paper order:

* §4.1 `lem:kovac-moment` (line 990) and the displays of its proof `eq:k-S`, `eq:k-Sprime`,
  `eq:k-Ssecond` (lines 1023, 1078, 1111), together with the four proof steps linking them
  (`KovacMoment_reflection`, `KovacMoment_identity`, `KovacMoment_reduction`, `KovacS_le_S1S2`).
* The proof-internal claims of **Theorem 1.1** (`thm:small-upper`, stated at line 140 in the §1
  module), lines 1118–1148: `SmallUpper_emptyCase`, `SmallUpper_markov`, `SmallUpper_momentStep`,
  `SmallUpper_paramChoice`, `SmallUpper_doubleExpPower`.
* §4.2 the unlabeled proposition "`f(n) ≤ n/10 ⟹ n > 10^{120}`" (line 1156) with its three proof
  steps, and the `lcm(1, …, 289)` remark (lines 1183–1195).
* §4.3 `eq:sv-basic` (1212), the construction target (1217–1222), `eq:sv-D` (1226), the family
  `𝒜₀(X)` of `eq:sv-factorization` (1231–1243), and the unlabeled lemma on it (1245–1258) with
  `eq:sv-two-sided`, split into its four assertions, plus two proof steps.

## Encoding decisions that apply throughout

* **`f` is junk `0` off `𝓡`**: every statement about `f` conjoins `N ∈ R` (see `smallRatioSet`
  in `S1_Main`, `Prop_SmallRatioThreshold`, `Eq_SvBasic`, `Rem_Lcm289Witness`).
* **Sums over `j ≥ 0`** of `(σ_j(n)/n)^q` are taken over `j < τ(n)`: for `j ≥ τ(n)` the paper's
  `σ_j(n) = 0` and `0^q = 0` (`q ≥ 1`), so nothing is lost (`S4a.prefixMoment`).
* **Infinite sums over `q`-tuples** (`S`, `S'`, `S''` in the proof of `lem:kovac-moment`) are encoded
  by their truncations to the box `[1, B]`, with the bound required **uniformly in `B`**. The terms
  are nonnegative, so this is equivalent to "summable and the sum is bounded", and it avoids the
  `tsum = 0` junk value of a non-summable series (which would make a `≤` claim vacuous).
* **`𝒜₀(X)` depends on `δ` only through `D`**: the paper's definition (lines 1231–1243) never
  mentions `δ`; `δ` enters by the choice of `D` in `eq:sv-D`. So the family is `S4a.A0 D X`, and
  every statement about it quantifies `∀ δ ∈ (0,1], ∀ D, SvDcond δ D → …`. Quantifying over *every*
  admissible `D` (rather than the one the paper fixes) is what the proof delivers — it uses of `D`
  only `D ∣ t` and `σ(D)/D > 1 + λ` — and it is what later consumers need.
* `ζ(2)` is written `Real.pi ^ 2 / 6` (Mathlib `hasSum_zeta_two`), as in `Inputs.Std_totient_sigma`.

## Pinned-Mathlib audit for this section (v4.31.0, 2026-09-25)

Nothing here is in Mathlib as a result about `σ_j`, `f`, prefix sums or moments. Standard facts the
proofs use that **are** in the pinned Mathlib (consumers should use these names, not restatements):
`Nat.abundancyIndex_le_of_dvd` (`σ(n)/n` is nondecreasing under divisibility, line 1289; `ℚ`-valued
`Nat.abundancyIndex`), `Nat.Coprime.sum_divisors_mul` / `ArithmeticFunction.isMultiplicative_sigma`
(Euler products for `σ(m)/m`, lines 1184–1187, 1229), `Nat.divisors_mul`
(`divisors (a*b) = divisors a * divisors b`, pointwise, for **all** `a, b` — the tool for the
non-coprime submultiplicativity at line 1292), `Nat.sum_div_divisors` (the involution `d ↦ n/d`
behind divisor reflection, line 1006), `harmonic_le_one_add_log` and
`log_add_one_le_harmonic` (lines 1169–1170, 1262–1272), `Nat.Primes.not_summable_one_div`
(`∏_{p ≤ z}(1 + 1/p)` unbounded, line 1229), `hasSum_zeta_two` (`ζ(2) = π²/6`), and
`Nat.lcmUpto` (`= lcmUpTo` at a natural argument). Mathlib has **no** Robin/Axler inequality (that
is `Inputs.Cite_Axler_Cor2`). The comparator-certified masters (`Erdos1054_3rdMomentProof.lean`)
contain `moment_le`, a third moment of `g_e(n)` for a *fixed cofactor* — a different object from the
all-`j` prefix moment of `lem:kovac-moment`; nothing there proves a result of this section.

## Numerics re-checked (exact rational arithmetic, Python `fractions`/`sympy`, 2026-09-25)

For `m = lcm(1, …, 289)` (128 digits): `σ(m)/m = 10.0047357412…`, `σ(m) = 3.0781522093…·10^{128}`,
`m/σ(m) = 0.0999526650…` — all three truncations printed in the paper are correct. (For
`lcm(1, …, 288)` the abundancy is `9.972…`, so 289 is the first cutoff that works.) Axler's bound at
`m = 10^{119}`: `(1 + 3.15367·10^{-7}) e^γ log log 10^{119} = 9.997440…  ≤ 9.99745`.
`H_{5040} = 9.1025…`, `1 + log 5040 = 9.5252… < 10`.
-/

namespace Principia.Erdos1054

open Finset

/-! ## Section-local objects -/

namespace S4a

/-- `∑_{j ≥ 0} (σ_j(n)/n)^q` — the inner sum of `lem:kovac-moment` (EP1054.tex line 995).
The paper's sum runs over all `j ≥ 0`; for `j ≥ τ(n)` it has `σ_j(n) = 0` (definition, line 343),
so for `q ≥ 1` only `j < τ(n)` contribute. -/
noncomputable def prefixMoment (q n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n.divisors.card, ((sigmaPrefix j n : ℝ) / n) ^ q

/-- The truncation to `r, a_i ≤ B` of `S = ∑_{r, a_1, …, a_q ≥ 1, r ≤ min_i a_i}
1/(a_1⋯a_q · lcm(r, a_1, …, a_q))` (`eq:k-S`, line 1024). Tuples are `a : Fin q → ℕ`;
`lcm(r, a_1, …, a_q)` is `Nat.lcm r (lcm_i a_i)`. -/
noncomputable def kovacS (q B : ℕ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 B,
    ∑ a ∈ (Fintype.piFinset fun _ : Fin q => Finset.Icc 1 B).filter (fun a => ∀ i, r ≤ a i),
      1 / ((∏ i, (a i : ℝ)) * (Nat.lcm r ((Finset.univ : Finset (Fin q)).lcm a) : ℝ))

/-- The truncation to `r ≤ B` of `S' = ∑_{r ≥ 1} r^{-2} (∑_{d ∣ r} d^{-(q-1)/q})^q` (line 1046). -/
noncomputable def kovacS1 (q B : ℕ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 B,
    1 / (r : ℝ) ^ 2 * (∑ d ∈ r.divisors, 1 / (d : ℝ) ^ (((q : ℝ) - 1) / q)) ^ q

/-- The truncation to `c_i ≤ B` of `S'' = ∑_{c_1, …, c_q ≥ 1}
1/(c_1^{(q-1)/q} ⋯ c_q^{(q-1)/q} · lcm(c_1, …, c_q))` (line 1051). -/
noncomputable def kovacS2 (q B : ℕ) : ℝ :=
  ∑ c ∈ Fintype.piFinset (fun _ : Fin q => Finset.Icc 1 B),
    1 / ((∏ i, (c i : ℝ) ^ (((q : ℝ) - 1) / q)) *
      (((Finset.univ : Finset (Fin q)).lcm c : ℕ) : ℝ))

/-- The paper's parameter choice `q = ⌊exp((1/δ)^c)⌋` (line 1136). -/
noncomputable def qChoice (c δ : ℝ) : ℕ := ⌊Real.exp ((1 / δ) ^ c)⌋₊

/-- The condition `eq:sv-D` on the fixed integer `D` (line 1225–1228): `D` squarefree and
`σ(D)/D > 1 + λ` with `λ = 1/δ`. (`Squarefree 0` is false, so `D ≥ 1`.) -/
def SvDcond (δ : ℝ) (D : ℕ) : Prop := Squarefree D ∧ 1 + 1 / δ < abundancy D

/-- The parameter conditions of `eq:sv-factorization` (lines 1235–1242) on a tuple `(p, q, r, k)`:
`p, q, r` prime; `k = D j` with `X^{1/120} < k ≤ X^{1/60}` and `σ(j)/j ≤ 4ζ(2)`;
`X^{1/15} < r ≤ X^{1/12}`; `X^{7/20} < q ≤ X^{11/30}`; `X/(2qrk) < p ≤ X/(qrk)`.
The paper's `ℓ = rk` and `n = qℓ` are written `r * k` and `q * r * k` by consumers. -/
def A0Tuple (D : ℕ) (X : ℝ) (p q r k : ℕ) : Prop :=
  p.Prime ∧ q.Prime ∧ r.Prime ∧
  (∃ j : ℕ, k = D * j ∧ abundancy j ≤ 4 * (Real.pi ^ 2 / 6)) ∧
  X ^ ((1 : ℝ) / 120) < (k : ℝ) ∧ (k : ℝ) ≤ X ^ ((1 : ℝ) / 60) ∧
  X ^ ((1 : ℝ) / 15) < (r : ℝ) ∧ (r : ℝ) ≤ X ^ ((1 : ℝ) / 12) ∧
  X ^ ((7 : ℝ) / 20) < (q : ℝ) ∧ (q : ℝ) ≤ X ^ ((11 : ℝ) / 30) ∧
  X / (2 * (q : ℝ) * r * k) < (p : ℝ) ∧ (p : ℝ) ≤ X / ((q : ℝ) * r * k)

open Classical in
/-- **The family `𝒜₀(X)`** (`eq:sv-factorization`, lines 1231–1243): the integers `M = pqrk` with
`(p, q, r, k)` satisfying `A0Tuple D X`. Filtering `[1, ⌊X⌋]` loses nothing: a valid tuple has
`pqrk ≤ X` (from `p ≤ X/(qrk)`) and `pqrk ≥ 1` (primes, and `k > X^{1/120} > 0`). The dependence on
`δ` is through `D` only (see the module docstring). -/
noncomputable def A0 (D : ℕ) (X : ℝ) : Finset ℕ :=
  (Finset.Icc 1 ⌊X⌋₊).filter (fun M => ∃ p q r k : ℕ, A0Tuple D X p q r k ∧ M = p * q * r * k)

end S4a

open S4a

/-! ## §4.1 Kovač's moment lemma -/

-- deps: KovacMoment_reduction (⇐ KovacMoment_identity ⇐ KovacMoment_reflection), Eq_KS.
-- used by: SmallUpper_momentStep (proof of thm:small-upper, lines 1128–1133).
/-- **`lem:kovac-moment`**, EP1054.tex line 990.
"There is an absolute constant $C>0$ such that, for every integer $q\geq3$ and every real $x\geq1$,
\[ \sum_{n\leq x}\sum_{j\geq0} \left(\frac{\sigma_j(n)}n\right)^q \ll \exp(Cq\log\log q)x. \]
The implicit constant is absolute."

Encoding: `∃ C > 0, ∃ K` (the absolute implied constant) **before** `∀ q ≥ 3, ∀ x ≥ 1`, so both are
uniform in `q` and `x`. `n` runs over `1 ≤ n ≤ ⌊x⌋`; the inner sum is `S4a.prefixMoment q n`
(all `j ≥ 0`, see its docstring). `log log q > 0` for `q ≥ 3`. -/
def Lem_KovacMoment : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ K : ℝ, ∀ q : ℕ, 3 ≤ q → ∀ x : ℝ, 1 ≤ x →
    ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, prefixMoment q n ≤
      K * Real.exp (C * (q : ℝ) * Real.log (Real.log (q : ℝ))) * x

-- deps: the sorted-prefix bridge (`prefixSumDivisors_eq_Fdiv` / `take_sort_toFinset`, Basic.lean:
--       the first τ(n)−j sorted divisors are the divisors of rank < τ(n)−j); the involution
--       d ↦ n/d on divisors (`Nat.sum_div_divisors`, Mathlib; it reverses rank, the same step as
--       the proof of `reflection` in Basic.lean, which states the F_e(d)-form eq:reflection, not
--       this σ_j-form).
-- used by: KovacMoment_identity.
/-- **Proof step of `lem:kovac-moment`** (unlabeled display, EP1054.tex lines 1003–1009).
"Let \[ 1=r_1<r_2<\cdots<r_{\tau(n)}=n \] be the divisors of $n$. Divisor reflection gives
\[ \frac{\sigma_j(n)}n=\sum_{i>j}\frac1{r_i}. \]"

Encoding: the index `i` of a divisor `r ∣ n` is `1 + #{d ∣ n : d < r}` (the divisors are listed in
increasing order from `r_1 = 1`), so `i > j` is `j ≤ #{d ∣ n : d < r}`. Stated for every `j ≥ 0`,
the paper's range for `σ_j` (line 338): for `j ≥ τ(n)` both sides are `0` (`sigmaPrefix` is `0`
there, and no divisor has `≥ τ(n)` divisors below it). `σ_j(n)/n` is real division, `n ≥ 1`. -/
def KovacMoment_reflection : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ j : ℕ,
    (sigmaPrefix j n : ℝ) / n =
      ∑ r ∈ n.divisors.filter (fun r => j ≤ (n.divisors.filter (· < r)).card), (1 : ℝ) / r

-- deps: KovacMoment_reflection, the multinomial expansion of the q-th power, and counting
--       thresholds (a tuple of divisors with minimum a is counted for the j with
--       0 ≤ j < rank(a) = #{r ∣ n : r ≤ a}).
-- used by: KovacMoment_reduction.
/-- **Proof step of `lem:kovac-moment`** (unlabeled display, EP1054.tex lines 1010–1019).
"After expanding the $q$th power and summing over $j$, a fixed tuple $a_1,\ldots,a_q$ of divisors is
counted once for each divisor threshold not exceeding $\min_i a_i$. Hence
\[ \sum_{j\geq0}\left(\frac{\sigma_j(n)}n\right)^q = \sum_{\substack{r,a_1,\ldots,a_q\mid n\\
 r\leq\min(a_1,\ldots,a_q)}} \frac1{a_1\cdots a_q}. \]"

Encoding: for `q ≥ 3` (the lemma's range) and `n ≥ 1`; tuples `a : Fin q → ℕ` of divisors of `n`. -/
def KovacMoment_identity : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∀ n : ℕ, 1 ≤ n →
    prefixMoment q n =
      ∑ r ∈ n.divisors,
        ∑ a ∈ (Fintype.piFinset fun _ : Fin q => n.divisors).filter (fun a => ∀ i, r ≤ a i),
          1 / ∏ i, (a i : ℝ)

-- deps: KovacMoment_identity; #{n ≤ x : L ∣ n} ≤ x/L.
-- used by: Lem_KovacMoment (with Eq_KS).
/-- **Proof step of `lem:kovac-moment`** (EP1054.tex lines 1020–1022).
"Summing over $n\leq x$ and bounding the number of multiples of $\lcm(r,a_1,\ldots,a_q)$ by
$x/\lcm(r,a_1,\ldots,a_q)$, it is enough to prove \eqref{eq:k-S}."

Encoding: the sum is bounded by `x` times the truncation of `S` at `B = ⌊x⌋` — exact, because every
divisor of an `n ≤ x` is `≤ ⌊x⌋`. With `Eq_KS` (uniform in `B`) this gives `Lem_KovacMoment`. -/
def KovacMoment_reduction : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∀ x : ℝ, 1 ≤ x →
    ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, prefixMoment q n ≤ x * kovacS q ⌊x⌋₊

-- deps: KovacS_le_S1S2, Eq_KSprime, Eq_KSsecond ("Combining (k-Sprime) and (k-Ssecond) proves
--       (k-S)", line 1114).
-- used by: Lem_KovacMoment.
/-- **`eq:k-S`**, EP1054.tex line 1023.
"\[ S:=\sum_{\substack{r,a_1,\ldots,a_q\geq1\\r\leq\min_i a_i}}
 \frac1{a_1\cdots a_q\lcm(r,a_1,\ldots,a_q)} \ll\exp(Cq\log\log q). \]"

Encoding: every truncation `S4a.kovacS q B` is bounded, uniformly in `B` (equivalent to the
infinite sum being finite and bounded — the terms are nonnegative); `∃ C > 0, ∃ K` before
`∀ q ≥ 3` (the constants of the lemma are absolute). -/
def Eq_KS : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ K : ℝ, ∀ q : ℕ, 3 ≤ q → ∀ B : ℕ,
    kovacS q B ≤ K * Real.exp (C * (q : ℝ) * Real.log (Real.log (q : ℝ)))

-- deps: the substitution b_i = r/gcd(r,a_i), c_i = a_i/gcd(r,a_i), lcm(r,a_1..a_q) = r·lcm(c_i),
--       and 1/c_i ≤ 1/(b_i^{1-β} c_i^β) for c_i ≥ b_i, β = (q-1)/q (lines 1028–1044).
-- used by: Eq_KS.
/-- **Proof step of `lem:kovac-moment`** (EP1054.tex lines 1028–1053).
"For each $i$, put $b_i=r/\gcd(r,a_i)$, $c_i=a_i/\gcd(r,a_i)$. … Dropping the coprimality
conditions and taking $\beta=(q-1)/q$ … Replacing each divisor $b_i\mid r$ by $r/d_i$ and using
$\beta q=q-1$ leaves the power $r^{-2}$. Thus $S\leq S'S''$."

Encoding: at every truncation level `B` (the substitution maps `r, a_i ≤ B` into `r ≤ B`,
`c_i ≤ a_i ≤ B`, injectively). -/
def KovacS_le_S1S2 : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∀ B : ℕ, kovacS q B ≤ kovacS1 q B * kovacS2 q B

-- deps: Euler product S' = ∏_p L_p; for p ≤ q, L_p ≤ (1-p^{-2})^{-1}(1-p^{-(q-1)/q})^{-q};
--       ∑_{p≤q} p^{-(q-1)/q} ≤ q^{1/q} ∑_{p≤q} 1/p ≪ log log q (Std_Mertens2, Inputs);
--       for p > q, L_p = 1 + O(p^{-2}) (lines 1056–1077).
-- used by: Eq_KS.
/-- **`eq:k-Sprime`**, EP1054.tex line 1078. "\[ S'\ll\exp(Cq\log\log q). \]"
where $S'=\sum_{r\geq1}\frac1{r^2}\left(\sum_{d\mid r}\frac1{d^{(q-1)/q}}\right)^q$ (line 1046).

Encoding: truncations `S4a.kovacS1 q B` bounded uniformly in `B`; constants absolute. -/
def Eq_KSprime : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ K : ℝ, ∀ q : ℕ, 3 ≤ q → ∀ B : ℕ,
    kovacS1 q B ≤ K * Real.exp (C * (q : ℝ) * Real.log (Real.log (q : ℝ)))

-- deps: Euler product S'' = ∏_p M_p, M_p = ∑_h p^{-h}(A_h^q - A_{h-1}^q); for p ≤ q,
--       M_p ≤ (1-p^{-1})^{-1}(1-p^{-(q-1)/q})^{-q} and Std_Mertens2 (Inputs); for p > q the
--       mean-value theorem gives M_p - 1 ≪ q p^{-2+1/q} and ∑_{n>q} q n^{-2+1/q} ≪ 1
--       (lines 1082–1110).
-- used by: Eq_KS.
/-- **`eq:k-Ssecond`**, EP1054.tex line 1111. "\[ S''\ll\exp(Cq\log\log q). \]"
where $S''=\sum_{c_1,\ldots,c_q\geq1}\frac1{c_1^{(q-1)/q}\cdots c_q^{(q-1)/q}\lcm(c_1,\ldots,c_q)}$
(line 1051).

Encoding: truncations `S4a.kovacS2 q B` bounded uniformly in `B`; constants absolute. -/
def Eq_KSsecond : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ K : ℝ, ∀ q : ℕ, 3 ≤ q → ∀ B : ℕ,
    kovacS2 q B ≤ K * Real.exp (C * (q : ℝ) * Real.log (Real.log (q : ℝ)))

/-! ## Proof-internal claims of Theorem 1.1 (`thm:small-upper`, proof at lines 1118–1148)

`thm:small-upper` itself (line 140) is stated in the §1 module. Its proof composes:
`SmallUpper_emptyCase` (the case `δX < 1`), `SmallUpper_momentStep` (from `SmallUpper_markov` and
`Lem_KovacMoment`), `SmallUpper_paramChoice` (the double-exponential bound), and
`SmallUpper_doubleExpPower` (the "in particular `O_M(δ^M X)`" clause).

The paper's `𝓔_δ(X) = {N ≤ X : N ∈ 𝓡, f(N) ≤ δ N}` (line 1121) is `smallRatioSet δ ∩ [1, X]`
(`S1_Main`), counted by `cnt (smallRatioSet δ) X` — the very set `Thm_SmallUpper_doubleExp` is
stated about, so these steps compose into it with no bridge. (Until 2026-09-25 this module carried
a verbatim copy `S4a.Eset` of `smallRatioSet`, because `S1_Main` was unbuilt.) -/

-- deps: f N ≥ 1 for N ∈ 𝓡 (`f_mem_Fform`, Basic.lean).
-- used by: thm:small-upper (the case δX < 1).
/-- **Proof step of `thm:small-upper`** (EP1054.tex line 1124).
"If $\delta X<1$, then $\mathcal{E}_\delta(X)$ is empty".

Encoding: `cnt (smallRatioSet δ) X = 0`, for `δ > 0`. -/
def SmallUpper_emptyCase : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ X : ℝ, δ * X < 1 → cnt (smallRatioSet δ) X = 0

-- deps: `f_mem_Fform` / the definition of f (the minimiser n = f(N) represents N, so
--       N = σ_j(n) for some 0 ≤ j < τ(n)); injectivity of N ↦ (f(N), j).
-- used by: SmallUpper_momentStep.
/-- **Proof step of `thm:small-upper`** (EP1054.tex lines 1124–1131), the moment (Markov) step.
"assume $\delta X\geq1$. If $N\in\mathcal{E}_\delta(X)$ and $n=f(N)$, then $n\leq\delta X$ and
$N=\sigma_j(n)$ for some $j\geq0$ with $\sigma_j(n)/n\geq1/\delta$. Therefore, for every integer
$q\geq3$, \[ \#\mathcal{E}_\delta(X) \leq\delta^q\sum_{n\leq\delta X}\sum_{j\geq0}
\left(\frac{\sigma_j(n)}n\right)^q \]"

Encoding: `δ > 0`, `δX ≥ 1` kept as in the paper; `n` runs over `[1, ⌊δX⌋]`. -/
def SmallUpper_markov : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ X : ℝ, 1 ≤ δ * X → ∀ q : ℕ, 3 ≤ q →
    (cnt (smallRatioSet δ) X : ℝ) ≤ δ ^ q * ∑ n ∈ Finset.Icc 1 ⌊δ * X⌋₊, prefixMoment q n

-- deps: SmallUpper_markov, Lem_KovacMoment (applied at x = δX ≥ 1).
-- used by: thm:small-upper (with SmallUpper_paramChoice).
/-- **Proof step of `thm:small-upper`** (EP1054.tex lines 1129–1133), the second line of the display:
"\[ \#\mathcal{E}_\delta(X) \ll\delta^{q+1}\exp(Cq\log\log q)X. \]"

Encoding: `∃ C > 0, ∃ K` (from `lem:kovac-moment`, absolute) before `∀ δ, X, q`. -/
def SmallUpper_momentStep : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ K : ℝ, ∀ δ : ℝ, 0 < δ → ∀ X : ℝ, 1 ≤ δ * X → ∀ q : ℕ, 3 ≤ q →
    (cnt (smallRatioSet δ) X : ℝ) ≤
      K * δ ^ (q + 1) * Real.exp (C * (q : ℝ) * Real.log (Real.log (q : ℝ))) * X

-- deps: elementary real analysis (C log log q ≤ c C log(1/δ) ≤ ½ log(1/δ) once c ≤ 1/(2C);
--       (q/2) log(1/δ) ≥ exp((1/δ)^{c/2}) for small δ).
-- used by: thm:small-upper (with SmallUpper_momentStep; the paper then renames c/2 as c).
/-- **Proof step of `thm:small-upper`** (EP1054.tex lines 1134–1145), the parameter choice.
"Choose a sufficiently small absolute $c>0$ and put $q=\left\lfloor\exp((1/\delta)^c)\right\rfloor$.
For all sufficiently small $\delta$, one has $C\log\log q\leq\tfrac12\log(1/\delta)$, and hence
\[ \delta^{q+1}\exp(Cq\log\log q) \leq\exp\!\left(-\frac q2\log\frac1\delta\right)
\leq\exp\!\left(-\exp((1/\delta)^{c/2})\right). \]"

Encoding: for the lemma's constant `C > 0`, `∃ c > 0` (depending only on `C`, hence absolute) and
`∃ δ₀ > 0` with: for `0 < δ ≤ δ₀`, `q = S4a.qChoice c δ` satisfies `q ≥ 3` (so the lemma applies)
and the outer inequality. The intermediate `exp(-(q/2) log(1/δ))` is folded away. -/
def SmallUpper_paramChoice : Prop :=
  ∀ C : ℝ, 0 < C → ∃ c : ℝ, 0 < c ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
    3 ≤ qChoice c δ ∧
      δ ^ (qChoice c δ + 1) *
          Real.exp (C * (qChoice c δ : ℝ) * Real.log (Real.log (qChoice c δ : ℝ))) ≤
        Real.exp (-Real.exp ((1 / δ) ^ (c / 2)))

-- deps: elementary (exp(-exp(t^c)) decays faster than any power of 1/t).
-- used by: thm:small-upper, "In particular" clause (line 148).
/-- **Proof step of `thm:small-upper`** (EP1054.tex lines 1145–1147).
"The fixed-power bound follows because this double-exponential expression is $O_M(\delta^M)$ for
every fixed $M>0$."

Encoding: `∀ c > 0, ∀ M > 0, ∃ K` (depending on `c, M`) uniform in `δ ∈ (0, 1]`. -/
def SmallUpper_doubleExpPower : Prop :=
  ∀ c : ℝ, 0 < c → ∀ M : ℝ, 0 < M → ∃ K : ℝ, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
    Real.exp (-Real.exp ((1 / δ) ^ c)) ≤ K * δ ^ M

/-! ## §4.2 Where are the small ratios? -/

-- deps: SmallRatio_prefixLeSig, SmallRatio_abundancySmall, Cite_Axler_Cor2 (Inputs),
--       SmallRatio_axlerNumeric; f(n) ≥ 1 and IsRep n (f n) for n ∈ 𝓡 (`f_mem_Fform`).
-- used by: nothing downstream (a quantitative remark; see Rem_Lcm289Abundant,
--          Rem_Lcm289Witness, Rem_Lcm289Values).
/-- **Unlabeled proposition**, EP1054.tex line 1156.
"If $n\in\Rcal$ and $f(n)\leq n/10$, then $n>10^{120}$."

Encoding: `n ∈ R` is essential (off `𝓡`, `f` is junk `0`, so e.g. `n = 2` would satisfy
`f(n) ≤ n/10` and violate the conclusion). `f(n) ≤ n/10` is compared in `ℝ` (no truncated
division); the conclusion `10^{120} < n` is in `ℕ`. -/
def Prop_SmallRatioThreshold : Prop :=
  ∀ n : ℕ, n ∈ R → (f n : ℝ) ≤ (n : ℝ) / 10 → 10 ^ 120 < n

-- deps: a prefix of the divisor list sums to at most the whole list (`prefixSumDivisors`).
-- used by: Prop_SmallRatioThreshold.
/-- **Proof step of the proposition at line 1156** (EP1054.tex line 1161).
"Every divisor-prefix sum of $m$ is at most $\sigma(m)$".

Encoding: `IsRep N m → N ≤ σ(m)` for all `N, m` (for `m = 0`, `IsRep N 0` is impossible). -/
def SmallRatio_prefixLeSig : Prop :=
  ∀ N m : ℕ, IsRep N m → N ≤ sig m

-- deps: σ(m)/m = ∑_{d∣m} 1/d ≤ H_{5040}; `harmonic_le_one_add_log` (Mathlib);
--       log 5040 < 9 (numeric).
-- used by: Prop_SmallRatioThreshold (the case m ≤ 5040).
/-- **Proof step of the proposition at line 1156** (EP1054.tex lines 1166–1171).
"If $m\leq5040$, then \[ \frac{\sigma(m)}m=\sum_{d\mid m}\frac1d \leq\sum_{d=1}^{5040}\frac1d
\leq1+\log5040<10, \] a contradiction."

Encoding: the conclusion `σ(m)/m < 10` for `1 ≤ m ≤ 5040`. -/
def SmallRatio_abundancySmall : Prop :=
  ∀ m : ℕ, 1 ≤ m → m ≤ 5040 → abundancy m < 10

-- deps: numeric evaluation (e^γ, log log 10^{119}); re-checked: the left side is 9.997440…
-- used by: Prop_SmallRatioThreshold (the case 5040 < m ≤ 10^{119}, with Cite_Axler_Cor2
--          (Inputs) and monotonicity of log log).
/-- **Proof step of the proposition at line 1156** (EP1054.tex lines 1172–1178), the numeric half:
"\[ \frac{\sigma(m)}m <(1+3.15367\cdot10^{-7})e^\gamma\log\log m \leq9.99745<10, \]"
for $m\leq10^{119}$.

Encoding: the value at the right end `m = 10^{119}` (the bound is increasing in `m > e`). -/
def SmallRatio_axlerNumeric : Prop :=
  (1 + 3.15367e-7) * Real.exp eulerGamma * Real.log (Real.log ((10 : ℝ) ^ 119)) ≤ 9.99745

-- deps: σ(m)/m = ∏_{p^a ∥ m} (1 + 1/p + … + 1/p^a) (`ArithmeticFunction.isMultiplicative_sigma`)
--       and a finite exact computation over the 61 primes ≤ 289.
-- used by: Rem_Lcm289Witness.
/-- **Remark after the proposition at line 1156** (EP1054.tex lines 1183–1187), the main claim.
"The obstruction is not vacuous. For $m=\lcm(1,\ldots,289)$, direct evaluation of the finite Euler
product for $\sigma(m)/m$ gives \[ \frac{\sigma(m)}m=10.004735741\ldots>10. \]"

Encoding: `10 < σ(m)/m` for `m = lcmUpTo 289` (`= Nat.lcmUpto 289`). -/
def Rem_Lcm289Abundant : Prop :=
  10 < abundancy (lcmUpTo 289)

-- deps: Rem_Lcm289Abundant; σ(m) is the full divisor-prefix sum of m (IsRep (σ m) m, k = τ(m)),
--       so σ(m) ∈ 𝓡 and f(σ(m)) ≤ m (`f_le_of_F` / the definition of f).
-- used by: nothing downstream (shows Prop_SmallRatioThreshold is not vacuous).
/-- **Remark after the proposition at line 1156** (EP1054.tex lines 1189–1195), the consequence.
"Thus $n=\sigma(m)$ satisfies \[ n=3.078152209\ldots\cdot10^{128}, \quad
\frac{f(n)}n\leq\frac m{\sigma(m)} =0.099952665\ldots<\frac1{10}. \]"

Encoding: with `m = lcmUpTo 289`: `σ(m) ∈ 𝓡` (needed, since `f` is junk off `𝓡`),
`f(σ(m))/σ(m) ≤ m/σ(m)`, and `m/σ(m) < 1/10`. The decimal values are `Rem_Lcm289Values`. -/
def Rem_Lcm289Witness : Prop :=
  sig (lcmUpTo 289) ∈ R ∧
    (f (sig (lcmUpTo 289)) : ℝ) / (sig (lcmUpTo 289) : ℝ) ≤
      (lcmUpTo 289 : ℝ) / (sig (lcmUpTo 289) : ℝ) ∧
    (lcmUpTo 289 : ℝ) / (sig (lcmUpTo 289) : ℝ) < 1 / 10

-- deps: finite exact computation (re-checked in Python, see the module docstring).
-- used by: nothing downstream.
/-- **Remark after the proposition at line 1156** (EP1054.tex lines 1187–1194), the printed digits:
$\sigma(m)/m=10.004735741\ldots$, $n=\sigma(m)=3.078152209\ldots\cdot10^{128}$,
$m/\sigma(m)=0.099952665\ldots$ for $m=\lcm(1,\ldots,289)$.

Encoding: "`x = a₁a₂…a_k…`" is read as the truncation `a ≤ x < a + 10^{-k}` at the last printed
digit. Separate from `Rem_Lcm289Abundant` so that the qualitative claim does not rest on digits. -/
def Rem_Lcm289Values : Prop :=
  (10.004735741 : ℝ) ≤ abundancy (lcmUpTo 289) ∧ abundancy (lcmUpTo 289) < 10.004735742 ∧
    3078152209 * 10 ^ 119 ≤ sig (lcmUpTo 289) ∧ sig (lcmUpTo 289) < 3078152210 * 10 ^ 119 ∧
    (0.099952665 : ℝ) ≤ (lcmUpTo 289 : ℝ) / (sig (lcmUpTo 289) : ℝ) ∧
    (lcmUpTo 289 : ℝ) / (sig (lcmUpTo 289) : ℝ) < 0.099952666

/-! ## §4.3 A positive-density family of abundant witnesses (lines 1198–1303) -/

-- deps: s(n) is the prefix sum of all divisors of n but n itself (k = τ(n) − 1 ≥ 1 for n ≥ 2),
--       so IsRep (s n) n; then the definition of f.
-- used by: the proof of thm:small-values (line 1878), via SvFamilyTarget (line 1222).
/-- **`eq:sv-basic`**, EP1054.tex line 1212.
"If $n\geq2$, then $s(n)$ is the sum of all proper divisors of $n$, so $s(n)\in\Rcal$ and
\[ f(s(n))\leq n \quad(n\geq2). \]"

Encoding: both assertions of the sentence; `s(n) ∈ R` is required for `f(s(n)) ≤ n` to mean
anything (junk `0` off `𝓡`). -/
def Eq_SvBasic : Prop :=
  ∀ n : ℕ, 2 ≤ n → aliquot n ∈ R ∧ f (aliquot n) ≤ n

-- deps: lem:sv-regular, lem:sv-classes, prop:sv-second-moment, Cauchy–Schwarz, eq:sv-two-sided
--       (the family A(X) ⊆ 𝒜₀(X) of lem:sv-regular; proof of thm:small-values, lines 1862–1883).
--       In Lean names (S4b_SmallValues): Claim_SvImageCount and Claim_SvWitness for a family
--       given by Lem_SvRegular.
-- used by: thm:small-values (Thm_SmallValues, S1_Main; with Eq_SvBasic: "rescaling X then proves
--          the theorem", line 1222).
/-- **Construction target of §4.3** (unlabeled, EP1054.tex lines 1217–1222).
"We will construct $\mathcal{A}(X)\subset[1,X]$ such that \[ n/\delta<s(n)\leq C_\delta X\quad
(n\in\mathcal{A}(X)), \quad \#s(\mathcal{A}(X))\gg_\delta X. \] By \eqref{eq:sv-basic}, rescaling
$X$ then proves the theorem."

Encoding: for `0 < δ ≤ 1` (the paper reduces to this range, line 1224), `∃ C_δ > 0, ∃ c > 0` (the
`≫_δ` constant) and `X₀` before `∀ X ≥ X₀`, then `∃ A ⊆ [1, X]` (a `Finset`). `s(𝒜(X))` is
`A.image aliquot`. The implication to `thm:small-values` is the spine's, not a separate `Prop`. -/
def SvFamilyTarget : Prop :=
  ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
    ∃ Cδ : ℝ, 0 < Cδ ∧ ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
      ∃ A : Finset ℕ, (∀ n ∈ A, 1 ≤ n ∧ (n : ℝ) ≤ X) ∧
        (∀ n ∈ A, (n : ℝ) / δ < (aliquot n : ℝ) ∧ (aliquot n : ℝ) ≤ Cδ * X) ∧
        c * X ≤ ((A.image aliquot).card : ℝ)

-- deps: `Nat.Primes.not_summable_one_div` (Mathlib: ∑ 1/p diverges, so ∏_{p≤z}(1+1/p) ≥ 1 + ∑ 1/p
--       is unbounded); D = ∏_{p ≤ z} p is squarefree with σ(D)/D = ∏_{p≤z}(1+1/p)
--       (`ArithmeticFunction.isMultiplicative_sigma`).
-- used by: Lem_SvA0Count, Lem_SvA0Unique, Eq_SvTwoSided, Lem_SvA0QLarge (their hypothesis),
--          and every later §4 statement about 𝒜₀(X) and 𝒜(X).
/-- **`eq:sv-D`**, EP1054.tex line 1226, as the existence claim made there.
"Put $\lambda=1/\delta$, and choose a fixed squarefree integer $D$ such that
\[ \frac{\sigma(D)}D>1+\lambda. \] Such a $D$ exists because $\prod_{p\leq z}(1+1/p)$ is
unbounded."

Encoding: the condition itself is `S4a.SvDcond δ D`; this `Prop` is its satisfiability for every
`δ ∈ (0, 1]` (the paper's range; it holds for every `δ > 0`). -/
def Eq_SvD : Prop :=
  ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∃ D : ℕ, SvDcond δ D

-- deps: SvA0_jSum (⇐ SvA0_sigmaHarmonic, `harmonic_le_one_add_log`, `log_add_one_le_harmonic`);
--       Std_primes_dyadic_lower (Inputs; primes p ∈ (T/2, T], T = X/(qrk) ≥ X^{8/15});
--       Std_Mertens2 (Inputs; ∑ 1/r over X^{1/15} < r ≤ X^{1/12}, ∑ 1/q over X^{7/20} < q ≤
--       X^{11/30}); Lem_SvA0Unique (distinct tuples give distinct M).
-- used by: lem:sv-regular (#𝒜(X) ≫_δ X after o(X) deletions, lines 1421–1458).
/-- **Unlabeled lemma on `𝒜₀(X)`**, EP1054.tex line 1245 — the count.
"There is a constant $C_\delta>0$ such that, for all sufficiently large $X$,
\[ \#\mathcal{A}_0(X)\gg_\delta X, \]"

Encoding: for every `δ ∈ (0, 1]` and every `D` satisfying `eq:sv-D` (the constant may depend on
`δ` and on `D`, which is a fixed function of `δ`), `∃ c > 0, ∃ X₀, ∀ X ≥ X₀, c X ≤ #𝒜₀(X)`. -/
def Lem_SvA0Count : Prop :=
  ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℕ, SvDcond δ D →
    ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → c * X ≤ ((A0 D X).card : ℝ)

-- deps: size separation: p > X^{1/2} (as X/(2qrk) ≥ X^{8/15}/2), q ∈ (X^{7/20}, X^{11/30}],
--       r ∈ (X^{1/15}, X^{1/12}], every prime factor of k ≤ X^{1/60} (lines 1285–1287).
-- used by: Lem_SvA0Count; lem:sv-regular ("the separated factor ranges make the decompositions
--          ℓ = rk, n = qℓ and M = pn unique", line 1449) and every later use of p, q, r, k of M.
/-- **Unlabeled lemma on `𝒜₀(X)`**, EP1054.tex lines 1251–1252 — unique factorization.
"every $M\in\mathcal{A}_0(X)$ has a unique factorization \eqref{eq:sv-factorization}"

Encoding: existence is membership in `S4a.A0`; uniqueness is stated as injectivity of
`(p, q, r, k) ↦ pqrk` on tuples satisfying `S4a.A0Tuple D X`, for all sufficiently large `X`
(the lemma's "for all sufficiently large X" governs all its assertions). The integer `j = k/D` is
then determined too. -/
def Lem_SvA0Unique : Prop :=
  ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℕ, SvDcond δ D →
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
      ∀ p q r k p' q' r' k' : ℕ, A0Tuple D X p q r k → A0Tuple D X p' q' r' k' →
        p * q * r * k = p' * q' * r' * k' → p = p' ∧ q = q' ∧ r = r' ∧ k = k'

-- deps: eq:sv-D (the condition S4a.SvDcond δ D); `Nat.abundancyIndex_le_of_dvd` (Mathlib: σ(n)/n
--       nondecreasing under divisibility, D ∣ t); SvA0_abundancySubmul; σ(j)/j ≤ 4ζ(2) from
--       S4a.A0Tuple; σ(p)/p = 1 + 1/p < 2 (lines 1289–1299).
-- used by: lem:sv-regular (eq:sv-image-abundancy, B_δ = C_δ + 2, line 1478);
--          prop:sv-second-moment; the proof of thm:small-values (f(N) ≤ M < δN, line 1878).
/-- **`eq:sv-two-sided`**, EP1054.tex line 1253 (part of the unlabeled lemma at line 1245).
"There is a constant $C_\delta>0$ such that, for all sufficiently large $X$, … and
\[ \lambda<\frac{s(t)}t<C_\delta \quad(t\in\{k,\ell,n,M\}). \]"

Encoding: `λ = 1/δ`; `ℓ = r k`, `n = q r k`, `M = p q r k` for a tuple satisfying
`S4a.A0Tuple D X`; `s(t)/t` is real division. `∃ C_δ > 0` before `∃ X₀`, uniform in `X` and in
the tuple. -/
def Eq_SvTwoSided : Prop :=
  ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℕ, SvDcond δ D →
    ∃ Cδ : ℝ, 0 < Cδ ∧ ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
      ∀ p q r k : ℕ, A0Tuple D X p q r k →
        ∀ t : ℕ, (t = k ∨ t = r * k ∨ t = q * r * k ∨ t = p * q * r * k) →
          1 / δ < (aliquot t : ℝ) / t ∧ (aliquot t : ℝ) / t < Cδ

-- deps: exponent arithmetic: ℓ = rk ≤ X^{1/12 + 1/60} = X^{1/10}, q^2 > X^{7/10} ≥ ℓ^7, so
--       q^9 > q^7 ℓ^7 = n^7 (lines 1299–1301).
-- used by: lem:sv-regular (the hypothesis P^+(n) > n^{7/9} of Cite_LP_Lemma22_range (Inputs),
--          line 1466).
/-- **Unlabeled lemma on `𝒜₀(X)`**, EP1054.tex line 1257. "Moreover, $q>n^{7/9}$."

Encoding: `n = q r k` for a tuple satisfying `S4a.A0Tuple D X`; `n^{7/9}` is a real power. -/
def Lem_SvA0QLarge : Prop :=
  ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℕ, SvDcond δ D →
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
      ∀ p q r k : ℕ, A0Tuple D X p q r k → ((q * r * k : ℕ) : ℝ) ^ ((7 : ℝ) / 9) < (q : ℝ)

-- deps: Lem_SvA0Count, Lem_SvA0Unique, Eq_SvTwoSided, Lem_SvA0QLarge.
-- used by: lem:sv-regular (line 1394 onward).
/-- **The unlabeled lemma on `𝒜₀(X)`**, EP1054.tex line 1245, in full.
"There is a constant $C_\delta>0$ such that, for all sufficiently large $X$,
\[ \#\mathcal{A}_0(X)\gg_\delta X, \] every $M\in\mathcal{A}_0(X)$ has a unique factorization
\eqref{eq:sv-factorization}, and \[ \lambda<\frac{s(t)}t<C_\delta \quad(t\in\{k,\ell,n,M\}). \]
Moreover, $q>n^{7/9}$."

Encoding: the conjunction of its four assertions. Each part carries its own `∃ X₀`; this is
equivalent to one common `X₀` (take the maximum), so nothing is weakened. -/
def Lem_SvA0 : Prop :=
  Lem_SvA0Count ∧ Lem_SvA0Unique ∧ Eq_SvTwoSided ∧ Lem_SvA0QLarge

-- deps: σ(j)/j^2 = ∑_{d a = j} 1/(d^2 a) (σ(j) = ∑_{d∣j} j/d) and ∑_{d ≤ J} 1/d^2 ≤ ζ(2)
--       (`hasSum_zeta_two`).
-- used by: SvA0_jSum.
/-- **Proof step of the lemma at line 1245** (EP1054.tex lines 1261–1266).
"For $J\geq1$, \[ \sum_{j\leq J}\frac{\sigma(j)}{j^2} =\sum_{d\leq J}\frac1{d^2}\sum_{a\leq J/d}
\frac1a \leq\zeta(2)\sum_{a\leq J}\frac1a. \]"

Encoding: the outer inequality, for natural `J ≥ 1` (a real `J` enters only through `⌊J⌋`). -/
def SvA0_sigmaHarmonic : Prop :=
  ∀ J : ℕ, 1 ≤ J →
    ∑ j ∈ Finset.Icc 1 J, (sig j : ℝ) / (j : ℝ) ^ 2 ≤
      Real.pi ^ 2 / 6 * ∑ a ∈ Finset.Icc 1 J, (1 : ℝ) / a

-- deps: SvA0_sigmaHarmonic; `harmonic_le_one_add_log`, `log_add_one_le_harmonic` (Mathlib);
--       the indicator bound 1[σ(j)/j > 4ζ(2)] ≤ (σ(j)/j)/(4ζ(2)).
-- used by: Lem_SvA0Count (the sum over k = Dj, line 1280).
open Classical in
/-- **Proof step of the lemma at line 1245** (EP1054.tex lines 1267–1273).
"Consequently, with $J_1=X^{1/120}/D$ and $J_2=X^{1/60}/D$,
\[ \sum_{\substack{J_1<j\leq J_2\\ \sigma(j)/j\leq4\zeta(2)}}\frac1j \geq \sum_{J_1<j\leq J_2}
\frac1j -\frac1{4\zeta(2)}\sum_{j\leq J_2}\frac{\sigma(j)}{j^2} \geq \left(\frac1{240}+o(1)\right)
\log X. \]"

Encoding: the outer inequality, with `o(1)` as `∀ ε > 0, ∃ X₀, ∀ X ≥ X₀, … ≥ (1/240 − ε) log X`,
for every fixed `D ≥ 1` (`X₀` may depend on `D`); `j` runs over naturals `J₁ < j ≤ J₂`. -/
def SvA0_jSum : Prop :=
  ∀ D : ℕ, 1 ≤ D → ∀ ε : ℝ, 0 < ε → ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X →
    ((1 : ℝ) / 240 - ε) * Real.log X ≤
      ∑ j ∈ (Finset.Icc 1 ⌊X ^ ((1 : ℝ) / 60) / D⌋₊).filter
          (fun j : ℕ => X ^ ((1 : ℝ) / 120) / D < (j : ℝ) ∧
            abundancy j ≤ 4 * (Real.pi ^ 2 / 6)),
        (1 : ℝ) / j

-- deps: `Nat.divisors_mul` (Mathlib.Data.Finset.NatDivisors: divisors (a*b) = divisors a * divisors b,
--       pointwise, for all a, b) with `Finset.mul_def` (= image of the product under (·*·)), then a
--       sum over an image is at most the sum over the domain for nonnegative terms
--       (`Finset.sum_image_le_of_nonneg`) and `Finset.sum_mul_sum`: σ(ab) ≤ σ(a)σ(b); divide by ab.
--       (The inequality itself is not in Mathlib; `Nat.Coprime.sum_divisors_mul` is the coprime
--       equality and does not apply to non-coprime a, b.)
-- used by: Eq_SvTwoSided (upper bound, lines 1292–1298).
/-- **Proof step of the lemma at line 1245** (EP1054.tex line 1292).
"The inequality $\sigma(ab)/(ab)\leq(\sigma(a)/a)(\sigma(b)/b)$ also gives …"

Encoding: for all `a, b ≥ 1` (the paper uses it without restriction). -/
def SvA0_abundancySubmul : Prop :=
  ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → abundancy (a * b) ≤ abundancy a * abundancy b

end Principia.Erdos1054
