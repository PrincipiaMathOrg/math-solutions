/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Erdos1054.Defs
import Principia.Erdos1054.Statements.Inputs
import Principia.Erdos1054.Statements.S4a_SmallUpper

set_option autoImplicit false

/-!
# Erdős 1054 (EP1054.tex) §4, part 2 — regularity, smooth-part classes, the collision estimate

**Statements only** for `Campaigns/Erdos-1054/collab-paper/EP1054.tex` **lines 1304–1887**: the
level `y(u)`, `Y`; `lem:LP-inputs`; `lem:smooth-part-input` (with the scale-free complete-period
count of its proof, `Eq_SmoothPartPeriodCount`); `lem:sv-regular`; `lem:sv-classes`;
`prop:sv-second-moment` together with the intermediate claims of its proof — every labeled display
(`eq:sv-k-reciprocal`, `eq:sv-m-reciprocal`, `eq:sv-collision`, `eq:sv-totient`,
`eq:sv-reduced-collision-sum`, `eq:sv-large-h-congruence`, `eq:sv-intermediate-totient`,
`eq:sv-f-sum`, `eq:sv-qr-sum`) and the unlabeled claims of the large-`h` and small-`h` cases; and
the intermediate claims of the proof of Theorem `thm:small-values` (lines 1862–1884). Every result
is a `def … : Prop`; nothing is asserted.

## Standing setup (paper lines 1224–1243, owned by S4a)

`0 < δ ≤ 1`, `λ = 1/δ`, and a fixed squarefree `D` with `σ(D)/D > 1 + λ` (`eq:sv-D`,
`S4a.SvDcond δ D`). As in S4a, every statement quantifies
`∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℕ, S4a.SvDcond δ D → …`: each result must hold for every admissible
choice of `D`. Constants written `≪_δ` may depend on `δ` and `D` (which the paper fixes in terms of
`δ`).

## How the abstract families are encoded

* `𝒜_0(X)` is S4a's `S4a.A0 D X` (a `Finset`, cut out of `[1, ⌊X⌋]`), with tuples
  `S4a.A0Tuple D X p q r k`. We follow S4a's spelling: `ℓ = r * k`, `n = q * r * k`,
  `M = p * q * r * k` (so S4a's `Eq_SvTwoSided` applies verbatim), and `pn` is written `p * n`.
* `𝒜(X)` (`lem:sv-regular`) is **abstract**: a family `𝒜 : ℝ → Finset ℕ` satisfying
  `SV.RegularFamily D 𝒜` (the lemma's listed properties with constants `c`, `B_δ` and a threshold
  `X₀`). `Lem_SvRegular` asserts such a family exists; every later statement is quantified over
  **every** family with those properties.
* `𝒟_X` (`lem:sv-classes`) is **abstract**: `SV.ClassesAt (𝒜 X) X c c₁ c₂ c₃ 𝒟` is that lemma's
  conclusion at one `X`. `Prop_SvSecondMoment` (stated "for `d ∈ 𝒟_X`") is quantified over every
  `𝒟` satisfying that conclusion, with the sv-classes constants as parameters.
* "For `M = pqrk ∈ 𝒜(X)` …" is encoded "for every tuple `(p, q, r, k)` with `S4a.A0Tuple` and
  `M = pqrk`"; S4a's `Lem_SvA0Unique` makes that tuple unique, so this is the paper's reading.
* Names: S4a's section-local objects live in the namespace `S4a` (`S4a.A0`, `S4a.A0Tuple`,
  `S4a.SvDcond`), but its paper results do not (`Lem_SvA0`, `Eq_SvTwoSided`, `SvFamilyTarget`,
  …); comments below cite each by its real Lean name.

`#𝒜(X)` is `(𝒜 X).card`; `𝒜_d(X)` is the finset `SV.classFin (𝒜 X) X d`; `s(𝒜(X))` is
`(𝒜 X).image aliquot`.
-/

namespace Principia.Erdos1054

open Finset Filter

/-! ## Section-local objects -/

namespace SV

/-- `y(u) = log log u / log log log u`, EP1054.tex lines 1306–1308 ("For `u` sufficiently large,
put …"). Junk for small `u`; every consumer takes `X` large. For natural `n`, `yOf n` is
definitionally `yLP n` (the `y(n)` of `lem:LP-inputs`, defined in `Statements.Inputs`). -/
noncomputable def yOf (u : ℝ) : ℝ := logIt 2 u / logIt 3 u

/-- `Y = y(X^{1/120})`, EP1054.tex line 1309. -/
noncomputable def Ycut (X : ℝ) : ℝ := yOf (X ^ ((1 : ℝ) / 120))

open Classical in
/-- `D_y(n)`, the largest `y`-smooth divisor of `n` (EP1054.tex line 1362 writes `D_Y(n)`; lines
1311–1312: "An integer is called `Y`-smooth if all of its prime factors are at most `Y`", which is
`IsSmooth`). Encoded as the `sup` of the finset of `y`-smooth divisors; for `n ≥ 1` that finset
contains `1`, so the `sup` is its maximum. `smoothPart y 0 = 0` (junk; `0` is never counted). -/
noncomputable def smoothPart (y : ℝ) (n : ℕ) : ℕ :=
  (n.divisors.filter (fun d => IsSmooth y d)).sup id

/-- `lem:sv-regular` (i)–(ii) at one level `t ∈ {k, ℓ, n, M}`, EP1054.tex lines 1399–1404:
"(i) `d = gcd(t, σ(t))`, and `d` is the largest `Y`-smooth divisor of both `t` and `s(t)`;
(ii) `σ(t)/d` is divisible by every prime at most `Y`, while every prime factor of `s(t)/d`
exceeds `y(t)`."
The divisions are exact once `d = gcd(t, σ(t))` (then `d ∣ σ(t)` and `d ∣ σ(t) − t = s(t)`).
`y(t)` is `yLP t`, the level of `lem:LP-inputs`. -/
def RegularAt (Y : ℝ) (d t : ℕ) : Prop :=
  d = Nat.gcd t (sig t) ∧ d = smoothPart Y t ∧ d = smoothPart Y (aliquot t) ∧
  (∀ p : ℕ, p.Prime → (p : ℝ) ≤ Y → p ∣ sig t / d) ∧
  IsRough (yLP t) (aliquot t / d)

/-- The square-divisibility exclusion at `n`, EP1054.tex lines 1406–1408 (and 1326–1330):
"`y(n) < q_0 ≤ n^{10/27}`, `q_0` prime `⟹ q_0^2 ∤ s(n)`." -/
def SqExcl (n : ℕ) : Prop :=
  ∀ q₀ : ℕ, q₀.Prime → yLP n < (q₀ : ℝ) → (q₀ : ℝ) ≤ (n : ℝ) ^ ((10 : ℝ) / 27) →
    ¬ q₀ ^ 2 ∣ aliquot n

end SV

/-- `eq:sv-LP25`, EP1054.tex lines 1411–1413 (inside `lem:sv-regular`), as a predicate of `X, n`:
"`∑_{a ∣ σ(n), a > (log log X)^2} 1/a ≤ 1`."
**Paper erratum, corrected here:** the sum runs over the **prime** divisors `r ∣ σ(n)`, as in
LP Lemma 2.5 (`Cite_LP_Lemma25`, whose docstring gives the source and a counterexample to the
all-divisors form, which would make `lem:sv-regular` unsatisfiable). The only consumer (lines
1640–1646, `Claim_SvA3Reduction`) removes *primes* from `A_{3,2}`, so needs only this form.
The threshold is `(log log X)^2`, not `(log log n)^2` (`n ≤ X`, so it only shrinks the sum relative
to `Cite_LP_Lemma25`). -/
def Eq_SvLP25 (X : ℝ) (n : ℕ) : Prop :=
  ∑ r ∈ (sig n).primeFactors.filter (fun r : ℕ => (logIt 2 X) ^ 2 < (r : ℝ)), (1 : ℝ) / r ≤ 1

/-- `eq:sv-image-abundancy`, EP1054.tex lines 1415–1417 (inside `lem:sv-regular`), as a predicate
of the constant `B = B_δ` and `n`: "`σ(s(n))/s(n) ≤ B_δ`." Real division; `abundancy m = σ(m)/m`. -/
def Eq_SvImageAbundancy (B : ℝ) (n : ℕ) : Prop := abundancy (aliquot n) ≤ B

namespace SV

/-- The listed properties of `lem:sv-regular` for one member `M` of `𝒜(X)`, EP1054.tex
lines 1396–1417, with `d = D_Y(M)` and `Y = Ycut X`. For every tuple `(p, q, r, k)` of
`eq:sv-factorization` with `M = pqrk` (unique by `Lem_SvA0Unique`), with `ℓ = rk`, `n = qrk`:
(i)–(ii) at each `t ∈ {k, ℓ, n, M}`; the square-divisibility exclusion at `n`; `eq:sv-LP25` at
`n`; `eq:sv-image-abundancy` at `n` with the constant `B`. -/
def RegularMember (D : ℕ) (B X : ℝ) (M : ℕ) : Prop :=
  ∀ p q r k : ℕ, S4a.A0Tuple D X p q r k → M = p * q * r * k →
    RegularAt (Ycut X) (smoothPart (Ycut X) M) k ∧
    RegularAt (Ycut X) (smoothPart (Ycut X) M) (r * k) ∧
    RegularAt (Ycut X) (smoothPart (Ycut X) M) (q * r * k) ∧
    RegularAt (Ycut X) (smoothPart (Ycut X) M) M ∧
    SqExcl (q * r * k) ∧
    Eq_SvLP25 X (q * r * k) ∧
    Eq_SvImageAbundancy B (q * r * k)

/-- "`𝒜(X)` is a regular subfamily" — the conclusion of `lem:sv-regular` (EP1054.tex
lines 1395–1418) for a family `𝒜 : ℝ → Finset ℕ`: there are constants `c > 0` (the `≫_δ` of
`#𝒜(X) ≫_δ X`) and `B = B_δ > 0` and a threshold `X₀` such that for `X ≥ X₀`:
`𝒜(X) ⊆ 𝒜_0(X)`, `#𝒜(X) ≥ c X`, and every member has the listed properties. -/
def RegularFamily (D : ℕ) (𝒜 : ℝ → Finset ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ B : ℝ, 0 < B ∧ ∃ X₀ : ℝ, ∀ X ≥ X₀,
    𝒜 X ⊆ S4a.A0 D X ∧ c * X ≤ ((𝒜 X).card : ℝ) ∧ ∀ M ∈ 𝒜 X, RegularMember D B X M

/-- `𝒜_d(X) = {M ∈ 𝒜(X) : d is the largest Y-smooth divisor of M}`, EP1054.tex
lines 1490–1491. -/
noncomputable def classFin (A : Finset ℕ) (X : ℝ) (d : ℕ) : Finset ℕ :=
  A.filter (fun M => smoothPart (Ycut X) M = d)

/-- `R_d(u) = #{M ∈ 𝒜_d(X) : s(M) = u}`, EP1054.tex line 1534. -/
noncomputable def Rd (A : Finset ℕ) (X : ℝ) (d u : ℕ) : ℕ :=
  ((classFin A X d).filter (fun M => aliquot M = u)).card

/-- The `k`-range of `eq:sv-factorization` in the class `d`: the integers
`X^{1/120} < k ≤ X^{1/60}` with `D_Y(k) = d` (EP1054.tex lines 1545–1552: "the corresponding
factor `k` is `d` times an integer with no prime factor at most `Y`"). The side conditions `D ∣ k`,
`σ(k/D)/(k/D) ≤ 4ζ(2)` are dropped: the reciprocal sums below are upper bounds, and the paper's
proof bounds the sum over this whole interval. -/
noncomputable def kSet (X : ℝ) (d : ℕ) : Finset ℕ :=
  (Finset.Iic ⌊X ^ ((1 : ℝ) / 60)⌋₊).filter
    (fun k : ℕ => X ^ ((1 : ℝ) / 120) < (k : ℝ) ∧ smoothPart (Ycut X) k = d)

/-- The primes in `(a, b]`. -/
noncomputable def primesIoc (a b : ℝ) : Finset ℕ :=
  (Finset.Iic ⌊b⌋₊).filter (fun p : ℕ => p.Prime ∧ a < (p : ℝ))

/-- `(p, q, r, k)` is the tuple of a member `M = pqrk` of the class `𝒜_d(X)` of the finset `A`
(EP1054.tex line 1562: "written as `M = pn`"). -/
def MemberTuple (D : ℕ) (A : Finset ℕ) (X : ℝ) (d p q r k : ℕ) : Prop :=
  S4a.A0Tuple D X p q r k ∧ p * q * r * k ∈ A ∧ smoothPart (Ycut X) (p * q * r * k) = d

/-- `n` is the `n`-part (`n = qrk`) of a member `M = pn ∈ 𝒜_d(X)` with large prime `p`
(EP1054.tex line 1562). -/
def IsNPart (D : ℕ) (A : Finset ℕ) (X : ℝ) (d p n : ℕ) : Prop :=
  ∃ q r k : ℕ, MemberTuple D A X d p q r k ∧ n = q * r * k

/-- `(n, n')` admits an off-diagonal collision (`eq:sv-collision`, EP1054.tex lines 1562–1566,
1655–1656): `n ≠ n'` and there are `p, p'` with `pn, p'n' ∈ 𝒜_d(X)` and `s(pn) = s(p'n')`. -/
def CollisionPair (D : ℕ) (A : Finset ℕ) (X : ℝ) (d n n' : ℕ) : Prop :=
  n ≠ n' ∧ ∃ p p' : ℕ, IsNPart D A X d p n ∧ IsNPart D A X d p' n' ∧
    aliquot (p * n) = aliquot (p' * n')

/-- `dh = gcd(s(n), s(n'))`, EP1054.tex line 1570. (`h = gcdS n n' / d`; exact, since
`d ∣ s(n)` and `d ∣ s(n')`.) -/
def gcdS (n n' : ℕ) : ℕ := Nat.gcd (aliquot n) (aliquot n')

/-- `A_3 = |σ(n) − σ(n')|/(dh)`, EP1054.tex line 1584. -/
def A3 (n n' : ℕ) : ℕ := Int.natAbs ((sig n : ℤ) - (sig n' : ℤ)) / gcdS n n'

/-- `m/φ(m)` (junk `0` at `m = 0`). -/
noncomputable def phiRatio (m : ℕ) : ℝ := (m : ℝ) / (m.totient : ℝ)

open Classical in
/-- `A'_{3,2}/φ(A'_{3,2})`, EP1054.tex lines 1631–1646: `A_{3,2}` is the part of `A_3` with prime
factors in `((log log X)^2, log X]`, and `A'_{3,2}` its largest divisor coprime to `σ(n)`. Encoded
through `m/φ(m) = ∏_{p ∣ m} p/(p−1)`: the product over primes `p ∣ A_3` in that range with
`p ∤ σ(n)`. -/
noncomputable def ratio32 (X : ℝ) (n n' : ℕ) : ℝ :=
  ∏ p ∈ (A3 n n').primeFactors.filter
      (fun p : ℕ => (logIt 2 X) ^ 2 < (p : ℝ) ∧ (p : ℝ) ≤ Real.log X ∧ ¬ p ∣ sig n),
    (p : ℝ) / ((p : ℝ) - 1)

open Classical in
/-- The number of prime pairs `(p, p')` realising a collision of the fixed pair `(n, n')`,
EP1054.tex lines 1588–1618: `#{(p, p') : pn, p'n' ∈ 𝒜_d(X), s(pn) = s(p'n')}` (`p, p' ≤ X`). -/
noncomputable def pairCount (D : ℕ) (A : Finset ℕ) (X : ℝ) (d n n' : ℕ) : ℕ :=
  ((Finset.Icc 1 ⌊X⌋₊ ×ˢ Finset.Icc 1 ⌊X⌋₊).filter
    (fun pp : ℕ × ℕ => IsNPart D A X d pp.1 n ∧ IsNPart D A X d pp.2 n' ∧
      aliquot (pp.1 * n) = aliquot (pp.2 * n'))).card

open Classical in
/-- The sum on the left of `eq:sv-reduced-collision-sum` (EP1054.tex lines 1648–1656), without
the prefactor `X log Y/(log X)^2`, restricted to collision pairs whose `h = gcd(s(n), s(n'))/d`
satisfies `H`: `∑_{n ≠ n'} (dh/(nn')) · A'_{3,2}/φ(A'_{3,2})`. (`n ≤ X^{7/15} ≤ X`, so the box
`[1, X]^2` contains every pair.) -/
noncomputable def reducedCollisionSum (D : ℕ) (A : Finset ℕ) (X : ℝ) (d : ℕ) (H : ℕ → Prop) : ℝ :=
  ∑ nn ∈ (Finset.Icc 1 ⌊X⌋₊ ×ˢ Finset.Icc 1 ⌊X⌋₊).filter
      (fun nn : ℕ × ℕ => CollisionPair D A X d nn.1 nn.2 ∧ H (gcdS nn.1 nn.2 / d)),
    (gcdS nn.1 nn.2 : ℝ) / ((nn.1 : ℝ) * (nn.2 : ℝ)) * ratio32 X nn.1 nn.2

end SV

/-- `eq:sv-class-size`, EP1054.tex lines 1494–1500 (inside `lem:sv-classes`), as a predicate of the
family at `X`, the constants and the class set `𝒟`:
"`c_1 X/(d log Y) ≤ #𝒜_d(X) ≤ c_2 X/(d log Y)`, `∑_{d∈𝒟_X} 1/d ≫_δ log Y`" (uniformly for
`d ∈ 𝒟`; `c₃` is the `≫_δ` constant). -/
def Eq_SvClassSize (A : Finset ℕ) (X : ℝ) (c₁ c₂ c₃ : ℝ) (𝒟 : Finset ℕ) : Prop :=
  (∀ d ∈ 𝒟, c₁ * (X / ((d : ℝ) * Real.log (SV.Ycut X))) ≤ ((SV.classFin A X d).card : ℝ) ∧
      ((SV.classFin A X d).card : ℝ) ≤ c₂ * (X / ((d : ℝ) * Real.log (SV.Ycut X)))) ∧
    c₃ * Real.log (SV.Ycut X) ≤ ∑ d ∈ 𝒟, (1 : ℝ) / d

/-- The conclusion of `lem:sv-classes` at one `X` (EP1054.tex lines 1487–1501), for the class set
`𝒟 = 𝒟_X`: its members are `Y`-smooth integers `1 ≤ d ≤ Y^c`; `eq:sv-class-size` holds; and the
image sets `s(𝒜_d(X))`, `d ∈ 𝒟`, are pairwise disjoint. -/
def SV.ClassesAt (A : Finset ℕ) (X : ℝ) (c c₁ c₂ c₃ : ℝ) (𝒟 : Finset ℕ) : Prop :=
  (∀ d ∈ 𝒟, 1 ≤ d ∧ IsSmooth (SV.Ycut X) d ∧ (d : ℝ) ≤ SV.Ycut X ^ c) ∧
    Eq_SvClassSize A X c₁ c₂ c₃ 𝒟 ∧
    ∀ d ∈ 𝒟, ∀ d' ∈ 𝒟, d ≠ d' →
      Disjoint ((SV.classFin A X d).image aliquot) ((SV.classFin A X d').image aliquot)

/-- `eq:sv-second-moment`, EP1054.tex lines 1537–1539, as a predicate of the family at `X`, the
class `d` and the constant `C`: "`∑_u R_d(u)^2 ≪_δ X/(d log Y)`". The sum over `u` runs over
`s(𝒜_d(X))`, outside which `R_d(u) = 0`. -/
def Eq_SvSecondMoment (A : Finset ℕ) (X : ℝ) (d : ℕ) (C : ℝ) : Prop :=
  ∑ u ∈ (SV.classFin A X d).image aliquot, ((SV.Rd A X d u : ℕ) : ℝ) ^ 2 ≤
    C * (X / ((d : ℝ) * Real.log (SV.Ycut X)))

/-! ## `lem:LP-inputs` -/

-- deps: Cite_LP_Lemma21 (parts (i)–(iv)), Cite_LP_Lemma22_range (square-divisibility),
--       Cite_LP_Lemma25 (reciprocal-divisor sum). No paper-internal dependency: this lemma IS the
--       literature. By construction it is the conjunction of the three inputs, verbatim.
-- used by: Lem_SvRegular (lines 1439, 1460, 1467); prop:sv-second-moment (line 1742).
/-- `lem:LP-inputs`, EP1054.tex line 1316.
"Put `y(n)=\log\log n/\log\log\log n`. Outside a set of integers of asymptotic density zero, the
following hold: (i) `v_p(\sigma(n))>v_p(n)` for every prime `p\leq y(n)`;
(ii) `P^+(\gcd(n,\sigma(n)))\leq y(n)`; (iii) `\sigma(n)/\gcd(n,\sigma(n))` is divisible by every
prime `p\leq y(n)`; (iv) every prime factor of `s(n)/\gcd(n,\sigma(n))` exceeds `y(n)`.
If in addition `P^+(n)>n^{7/9}`, then, outside another density-zero set,
`y(n)<q_0\leq n^{10/27}`, `q_0` prime `\Longrightarrow q_0^2\nmid s(n)`.
Finally, outside a set of asymptotic density zero,
`\sum_{a\mid\sigma(n),\,a>(\log\log n)^2} 1/a\leq1`."

Encoding: three exceptional sets, one per sentence, each `DensZero`; `y(n)` is `yLP n`;
`v_p = Nat.factorization`; `P^+(m) ≤ y` is `IsSmooth y m`; `P^+(n) > n^{7/9}` is
`∃ p ∈ n.primeFactors, n^{7/9} < p`. **Paper erratum, corrected here:** the last sum runs over the
**prime** divisors `r ∣ σ(n)` (LP's `r` denotes a prime; the all-divisors form is false; see
`Cite_LP_Lemma25`). The three conjuncts are exactly `Cite_LP_Lemma21`, `Cite_LP_Lemma22_range`,
`Cite_LP_Lemma25`, so the body is written as their conjunction: one statement per input, which
cannot drift from `Inputs`. (Until 2026-09-25 the body was a verbatim copy of the three input
bodies; the replacement was checked to be `Iff.rfl` to that copy.) -/
def Lem_LPInputs : Prop :=
  Cite_LP_Lemma21 ∧ Cite_LP_Lemma22_range ∧ Cite_LP_Lemma25

/-! ## `lem:smooth-part-input` -/

-- deps: elementary — for `Y`-smooth `d ≥ 1`, `D_y(n) = d ⟺ n = d·u` with `gcd(u, y#) = 1`
--       (`y#` = `primorialR y`); the count of `u ≤ ⌊T/d⌋` coprime to `P = y#` differs from
--       `(T/d)·φ(P)/P` by at most `φ(P) ≤ P` (complete periods mod `P`), and `Delta y = φ(P)/P`
--       — Notation_Delta_density (S1, first conjunct: `Defs.Delta` is the product
--       `∏_{p≤y}(1 − 1/p)`, so this identity is not definitional). Holds with `C = 1`.
-- used by: Lem_SmoothPartInput (y = Yf X, T = X); Eq_SvKReciprocal (y = SV.Ycut X, at every scale
--          T ∈ (X^{1/120}, X^{1/60}] with the level held fixed, line 1547).
/-- The complete-period count, EP1054.tex lines 1362–1369 (in the proof of
`lem:smooth-part-input`).
"Write `D_Y(n)` for the largest `Y`-smooth divisor of `n`. For a `Y`-smooth integer `d`,
`D_Y(n)=d` if and only if `n=du` with `\gcd(u,Y\#)=1`. Counting complete periods modulo `Y\#` gives
`\#\{n\leq X:D_Y(n)=d\}=\frac Xd\Delta(Y)+O(Y\#)`."

Encoding: **scale-free** — the level `y` and the counting scale `T` are independent variables, which
is what `eq:sv-k-reciprocal` needs ("applied uniformly throughout the fixed power interval for
`k`", line 1548: level `Y = Ycut X`, scales `T` up to `X^{1/60}`). `O(Y#)` is an absolute constant
`C` fixed before every other quantifier. `d ≥ 1` is explicit; `0 ≤ T` is needed (for `T < 0` the
count is `0` while `T Δ(y)/d` is not). -/
def Eq_SmoothPartPeriodCount : Prop :=
  ∃ C : ℝ, ∀ (y T : ℝ) (d : ℕ), 0 ≤ T → 1 ≤ d → IsSmooth y d →
    |(cnt {n : ℕ | SV.smoothPart y n = d} T : ℝ) - T / (d : ℝ) * Delta y| ≤
      C * (primorialR y : ℝ)

-- deps: Eq_SmoothPartPeriodCount (with y = Yf X, T = X); Std_Mertens3 (Δ(Y) ≍ 1/log Y);
--       Mathlib `primorial_le_four_pow` (Y# ≤ 4^Y = X^{o(1)} because Y = o(log X));
--       Std_Mertens1 (∑_{p≤Y} log p/(p−1) ≪ log Y; a derived input, Inputs section 4: the paper
--       gets it from Chebyshev by partial summation, line 1383); elementary: Legendre's
--       ∑_{n≤X} log D_Y(n) = ∑_{p≤Y} log p ∑_a ⌊X/p^a⌋, Markov's inequality.
-- used by: Lem_SvClasses (lines 1506–1518). (Eq_SvKReciprocal uses the scale-free period count
--          Eq_SmoothPartPeriodCount from this lemma's proof, not this statement: its counts are at
--          scales T ≠ X with the level fixed at SV.Ycut X.)
/-- `lem:smooth-part-input`, EP1054.tex line 1348.
"Suppose that `Y=Y(X)\to\infty` and `Y=o(\log X)`. For every fixed `c>0`, uniformly for `Y`-smooth
`d\leq Y^c`, `\#\{n\leq X:d\text{ is the largest $Y$-smooth divisor of }n\}\asymp X/(d\log Y)`.
Moreover, given `\eta>0`, `c` may be chosen sufficiently large that the integers `n\leq X` whose
largest `Y`-smooth divisor exceeds `Y^c` account for at most `\eta X` integers for all sufficiently
large `X`."

Encoding: `Y(X)` is an arbitrary function `Yf` with `Yf → ∞` and `Yf X ≤ ε log X` eventually for
every `ε > 0` (`o(log X)`; `Yf > 0` eventually). `≍` = two-sided bound with constants `c₁, c₂ > 0`
depending on the fixed `c` (and the fixed function `Yf`), uniform in `d` and valid for `X ≥ X₀`
("uniformly for …", implicitly for large `X`). `d ≥ 1` is explicit (`d = 0` is `IsSmooth`).
"`c` may be chosen sufficiently large" = `∃ c₀ > 0, ∀ c ≥ c₀`, the threshold `X₀` depending on `c`.
"Largest `Y`-smooth divisor" is `SV.smoothPart (Yf X)`. -/
def Lem_SmoothPartInput : Prop :=
  ∀ Yf : ℝ → ℝ, Tendsto Yf atTop atTop →
    (∀ ε : ℝ, 0 < ε → ∃ X₀ : ℝ, ∀ X ≥ X₀, Yf X ≤ ε * Real.log X) →
    (∀ c : ℝ, 0 < c → ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∃ X₀ : ℝ, ∀ X ≥ X₀, ∀ d : ℕ,
        1 ≤ d → IsSmooth (Yf X) d → (d : ℝ) ≤ Yf X ^ c →
          c₁ * (X / ((d : ℝ) * Real.log (Yf X))) ≤
              (cnt {n : ℕ | SV.smoothPart (Yf X) n = d} X : ℝ) ∧
            (cnt {n : ℕ | SV.smoothPart (Yf X) n = d} X : ℝ) ≤
              c₂ * (X / ((d : ℝ) * Real.log (Yf X)))) ∧
    (∀ η : ℝ, 0 < η → ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c : ℝ, c₀ ≤ c → ∃ X₀ : ℝ, ∀ X ≥ X₀,
        (cnt {n : ℕ | Yf X ^ c < (SV.smoothPart (Yf X) n : ℝ)} X : ℝ) ≤ η * X)

/-! ## `lem:sv-regular` -/

-- deps: partial summation (Mathlib `sum_mul_eq_sub_integral_mul`, AbelSummation) from
--       #(E ∩ [1,T]) = o(T). No paper-internal dependency.
-- used by: Lem_SvRegular (lines 1446–1458, 1472–1473).
open Classical in
/-- `eq:sv-harmonic-density-zero`, EP1054.tex lines 1443–1448 (in the proof of `lem:sv-regular`).
"let `\mathcal{E}\subseteq\N` satisfy `\#(\mathcal{E}\cap[1,T])=o(T)`. Partial summation gives
`\sum_{n\leq T,\ n\in\mathcal{E}} 1/n=o(\log T)`."

Encoding: hypothesis `DensZero E`; `o(log T)` = `∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, … ≤ ε log T`. -/
def Eq_SvHarmonicDensityZero : Prop :=
  ∀ E : Set ℕ, DensZero E → ∀ ε : ℝ, 0 < ε → ∃ T₀ : ℝ, ∀ T ≥ T₀,
    ∑ n ∈ (Finset.Icc 1 ⌊T⌋₊).filter (· ∈ E), (1 : ℝ) / n ≤ ε * Real.log T

-- deps: Lem_SvA0 (S4a, line 1245: Lem_SvA0Count #𝒜_0(X) ≫_δ X, Lem_SvA0Unique,
--       Eq_SvTwoSided with C_δ, Lem_SvA0QLarge q > n^{7/9}); Lem_LPInputs (at t = k, ℓ, n,
--       M; its square part at n; its reciprocal-divisor part at n); Eq_SvHarmonicDensityZero
--       (deletions at the levels k, ℓ, n cost o(X)); Cite_Pollack_Thm14 (the extra exclusion at n,
--       giving B_δ = C_δ + 2); Std_Mertens2 (∑_{Y<p≤y(X)} 1/p = o(1), and bounded reciprocal prime
--       sums over the power intervals for q, r); Chebyshev's upper bound π(T) ≪ T/log T (Mathlib
--       Chebyshev) for the count of p ∈ (T/2, T].
-- used by: Lem_SvClasses, Prop_SvSecondMoment and all its intermediate claims, the proof of
--          thm:small-values (via SvFamilyTarget, S4a).
/-- `lem:sv-regular`, EP1054.tex line 1394.
"There is a subfamily `\mathcal{A}(X)\subseteq\mathcal{A}_0(X)` with `\#\mathcal{A}(X)\gg_\delta X`
having the following properties. For `M=pqrk\in\mathcal{A}(X)`, let `d` be the largest `Y`-smooth
divisor of `M`. Then, for every `t\in\{k,\ell,n,M\}`, (i) `d=\gcd(t,\sigma(t))`, and `d` is the
largest `Y`-smooth divisor of both `t` and `s(t)`; (ii) `\sigma(t)/d` is divisible by every prime at
most `Y`, while every prime factor of `s(t)/d` exceeds `y(t)`. In addition,
`y(n)<q_0\leq n^{10/27}`, `q_0` prime `\Longrightarrow q_0^2\nmid s(n)`, and
`\sum_{a\mid\sigma(n),\,a>(\log\log X)^2} 1/a\leq1` (eq:sv-LP25). There is also a constant
`B_\delta>0` such that `\sigma(s(n))/s(n)\leq B_\delta` (eq:sv-image-abundancy)."

Encoding: under the standing setup, there is a family `𝒜 : ℝ → Finset ℕ` with
`SV.RegularFamily D 𝒜` — constants `c > 0` (`≫_δ`) and `B > 0` (`B_δ`) fixed before `X`, and for
all sufficiently large `X` (implicit in the paper) `𝒜(X) ⊆ 𝒜_0(X)`, `#𝒜(X) ≥ cX`, and the listed
properties (`SV.RegularMember`). A function `X ↦ 𝒜(X)` is the paper's "for each `X` a subfamily
`𝒜(X)`" after choice. -/
def Lem_SvRegular : Prop :=
  ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℕ, S4a.SvDcond δ D →
    ∃ 𝒜 : ℝ → Finset ℕ, SV.RegularFamily D 𝒜

/-! ## `lem:sv-classes` -/

-- deps: Lem_SvRegular (through the hypothesis `SV.RegularFamily`: #𝒜(X) ≥ ηX; property (i) at t = M,
--       which makes d = D_Y(s(M)) and hence the images disjoint — the remark at lines 1482–1484);
--       Lem_SmoothPartInput (with Yf = SV.Ycut: its upper bound and its tail, choosing c with tail
--       ≤ ηX/3); Std_Mertens3 (∑_{P^+(d)≤Y} 1/d = ∏_{p≤Y}(1−1/p)^{-1} ≍ log Y).
-- used by: Prop_SvSecondMoment (its hypothesis), Claim_SvClassImage, Claim_SvImageCount.
/-- `lem:sv-classes`, EP1054.tex line 1486.
"There are positive constants `c,c_1,c_2`, depending at most on `\delta`, and a set
`\mathcal{D}_X` of `Y`-smooth integers `d\leq Y^c` such that, writing
`\mathcal{A}_d(X)=\{M\in\mathcal{A}(X):d\text{ is the largest $Y$-smooth divisor of }M\}`, one has,
uniformly for `d\in\mathcal{D}_X`,
`c_1 X/(d\log Y)\leq\#\mathcal{A}_d(X)\leq c_2 X/(d\log Y)`,
`\sum_{d\in\mathcal{D}_X} 1/d\gg_\delta\log Y` (eq:sv-class-size).
The sets `s(\mathcal{A}_d(X))`, `d\in\mathcal{D}_X`, are pairwise disjoint."

Encoding: for every family with the properties of `lem:sv-regular` (`SV.RegularFamily D 𝒜`), there
are `c, c₁, c₂, c₃ > 0` (`c₃` the `≫_δ` constant) and `X₀` such that for `X ≥ X₀` some finite set
`𝒟` satisfies `SV.ClassesAt (𝒜 X) X c c₁ c₂ c₃ 𝒟`. The constants may depend on `δ, D` and on the
family (itself fixed in terms of `δ`). -/
def Lem_SvClasses : Prop :=
  ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℕ, S4a.SvDcond δ D →
    ∀ 𝒜 : ℝ → Finset ℕ, SV.RegularFamily D 𝒜 →
      ∃ c c₁ c₂ c₃ : ℝ, 0 < c ∧ 0 < c₁ ∧ 0 < c₂ ∧ 0 < c₃ ∧ ∃ X₀ : ℝ, ∀ X ≥ X₀,
        ∃ 𝒟 : Finset ℕ, SV.ClassesAt (𝒜 X) X c c₁ c₂ c₃ 𝒟

/-! ## `prop:sv-second-moment` -/

-- deps: diagonal ≤ #𝒜_d(X) ≤ c₂X/(d log Y) (Eq_SvClassSize, from the SV.ClassesAt hypothesis);
--       off-diagonal: Eq_SvCollision, Claim_SvSigmaDistinct, Claim_SvSievePairs, Eq_SvTotient
--       with Eq_SvImageAbundancy (the A_1, A_2 factors), Claim_SvA3Reduction,
--       Eq_SvReducedCollisionSum. Through these: Lem_SvRegular, Lem_SvClasses, Lem_LPInputs,
--       Lem_SmoothPartInput, Eq_SmoothPartPeriodCount, Eq_SvTwoSided (S4a), Cite_LP_sieve37,
--       Std_totient_sigma, Std_Mertens2, Std_Mertens3, Std_BrunTitchmarsh, Std_divisorBound.
-- used by: Claim_SvClassImage (proof of thm:small-values, line 1864).
/-- `prop:sv-second-moment`, EP1054.tex line 1531.
"For `d\in\mathcal{D}_X`, put `R_d(u)=\#\{M\in\mathcal{A}_d(X):s(M)=u\}`. Then, uniformly for
`d\in\mathcal{D}_X`, `\sum_u R_d(u)^2\ll_\delta X/(d\log Y)` (eq:sv-second-moment)."

Encoding: for every regular family `𝒜` and every choice of the `lem:sv-classes` constants
`c, c₁, c₂, c₃ > 0`, there are `C` and `X₀` such that for `X ≥ X₀`, **every** class set `𝒟`
satisfying the conclusion of `lem:sv-classes` at `X` (`SV.ClassesAt`), and every `d ∈ 𝒟`,
`Eq_SvSecondMoment (𝒜 X) X d C`. `C` is uniform in `X`, `𝒟` and `d`; it may depend on `δ, D`, the
family and the sv-classes constants (all fixed in terms of `δ`). -/
def Prop_SvSecondMoment : Prop :=
  ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℕ, S4a.SvDcond δ D →
    ∀ 𝒜 : ℝ → Finset ℕ, SV.RegularFamily D 𝒜 →
      ∀ c c₁ c₂ c₃ : ℝ, 0 < c → 0 < c₁ → 0 < c₂ → 0 < c₃ →
        ∃ C : ℝ, ∃ X₀ : ℝ, ∀ X ≥ X₀, ∀ 𝒟 : Finset ℕ, SV.ClassesAt (𝒜 X) X c c₁ c₂ c₃ 𝒟 →
          ∀ d ∈ 𝒟, Eq_SvSecondMoment (𝒜 X) X d C

/-! ### Intermediate claims of the proof of `prop:sv-second-moment` -/

-- deps: Eq_SmoothPartPeriodCount (with y = SV.Ycut X, at every scale T ∈ (X^{1/120}, X^{1/60}]:
--       the level stays fixed while the scale moves, so Lem_SmoothPartInput's single-scale
--       statement does not suffice), Std_Mertens3 (Δ(Y) ≍ 1/log Y with absolute constants),
--       Mathlib `primorial_le_four_pow` (Y# ≤ 4^Y = X^{o(1)}, so the period error
--       Y#/(X^{1/120}/d) = o(1) for d ≤ Y^c — this is where X₀ depends on c), partial summation.
-- used by: Eq_SvMReciprocal; Claim_SvSmallH (line 1829).
/-- `eq:sv-k-reciprocal`, EP1054.tex lines 1545–1552.
"Since `d` is the largest `Y`-smooth divisor of every member of `\mathcal{A}_d(X)`, the
corresponding factor `k` is `d` times an integer with no prime factor at most `Y`. The
complete-period count in Lemma smooth-part-input, applied uniformly throughout the fixed power
interval for `k`, and partial summation give `\sum_k 1/k\ll\log X/(d\log Y)`."

Encoding: the sum runs over the whole interval `X^{1/120} < k ≤ X^{1/60}` with `D_Y(k) = d`
(`SV.kSet`), which contains every `k`-factor of `𝒜_d(X)`; the bound is uniform for `Y`-smooth
`1 ≤ d ≤ Y^c` (the range of `𝒟_X`). The paper's `≪` is **unsubscripted** (contrast `≪_δ` at
lines 1538, 1612, 1653), so `C` is absolute and comes before `∀ c`; only the threshold `X₀`
depends on `c`. (True: the sum is `(Δ(Y) log X)/(120 d) + o(1/d)` and `Δ(Y) ≍ 1/log Y`.) -/
def Eq_SvKReciprocal : Prop :=
  ∃ C : ℝ, ∀ c : ℝ, 0 < c → ∃ X₀ : ℝ, ∀ X ≥ X₀, ∀ d : ℕ,
    1 ≤ d → IsSmooth (SV.Ycut X) d → (d : ℝ) ≤ SV.Ycut X ^ c →
      ∑ k ∈ SV.kSet X d, (1 : ℝ) / k ≤ C * (Real.log X / ((d : ℝ) * Real.log (SV.Ycut X)))

-- deps: Eq_SvKReciprocal; Std_Mertens2 (the reciprocal prime sums over (X^{7/20}, X^{11/30}] and
--       (X^{1/15}, X^{1/12}] are bounded, tending to log(22/21) and log(5/4)).
-- used by: Claim_SvSmallH (lines 1842, 1857).
/-- `eq:sv-m-reciprocal`, EP1054.tex lines 1553–1558.
"Here and below a sum over a factor of a member of `\mathcal{A}_d(X)` is restricted to the ranges
in (eq:sv-factorization). The reciprocal prime sums over the fixed power intervals for `q` and `r`
are bounded, so `\sum_n 1/n\ll\log X/(d\log Y)`."

Encoding: `∑_n 1/n` over `n = q r k` is the triple sum over primes `q ∈ (X^{7/20}, X^{11/30}]`,
primes `r ∈ (X^{1/15}, X^{1/12}]` and `k ∈ SV.kSet X d` (the map `(q, r, k) ↦ qrk` is injective on
these ranges, and the triple sum dominates the sum over actual `n`-parts). Uniform for `Y`-smooth
`1 ≤ d ≤ Y^c`. Unsubscripted `≪`: `C` absolute, before `∀ c`; `X₀` depends on `c`. -/
def Eq_SvMReciprocal : Prop :=
  ∃ C : ℝ, ∀ c : ℝ, 0 < c → ∃ X₀ : ℝ, ∀ X ≥ X₀, ∀ d : ℕ,
    1 ≤ d → IsSmooth (SV.Ycut X) d → (d : ℝ) ≤ SV.Ycut X ^ c →
      ∑ q ∈ SV.primesIoc (X ^ ((7 : ℝ) / 20)) (X ^ ((11 : ℝ) / 30)),
        ∑ r ∈ SV.primesIoc (X ^ ((1 : ℝ) / 15)) (X ^ ((1 : ℝ) / 12)),
          ∑ k ∈ SV.kSet X d, (1 : ℝ) / ((q : ℝ) * (r : ℝ) * (k : ℝ)) ≤
        C * (Real.log X / ((d : ℝ) * Real.log (SV.Ycut X)))

-- deps: elementary — σ is multiplicative (`ArithmeticFunction.isMultiplicative_sigma`),
--       σ(p) = p + 1, σ(n) ≥ n.
-- used by: Claim_SvSigmaDistinct, Claim_SvSievePairs, Claim_SvLargeHUnits and
--          Eq_SvLargeHCongruence (s(n) = q s(ℓ) + σ(ℓ); dh ∣ σ(n) − σ(n')),
--          Claim_SvSmallHResidues (σ(n) ≡ σ(n') mod h).
/-- `eq:sv-collision`, EP1054.tex lines 1562–1566.
"Consider an off-diagonal collision, written as `M=pn`, `M'=p'n'`, with `n\ne n'`. Then
`p\,s(n)+\sigma(n)=p'\,s(n')+\sigma(n')`."

Encoding: the display is `s(M) = s(M')` rewritten by the identity `s(pn) = p s(n) + σ(n)` for a
prime `p ∤ n` (here `p > X^{8/15}/2 > n`); that identity is what is stated. -/
def Eq_SvCollision : Prop :=
  ∀ p n : ℕ, p.Prime → ¬ p ∣ n → aliquot (p * n) = p * aliquot n + sig n

-- deps: Eq_SvTwoSided (S4a; s(n) < C_δ n ≤ C_δ X^{7/15}), S4a.A0Tuple (p > X^{8/15}/2),
--       Eq_SvCollision.
-- used by: Claim_SvSievePairs (nonzero determinant), the definition of A_3 (line 1584).
/-- Off-diagonal nondegeneracy, EP1054.tex lines 1572–1580 (unlabeled).
"This difference is nonzero. Indeed, equality would give `p s(n)=p's(n')`; for all sufficiently
large `X`, `\min(p,p')>\tfrac12X^{8/15}>C_\delta X^{7/15}\geq\max\{s(n),s(n')\}`, which forces
`p=p'`, then `s(n)=s(n')`, and finally `n=n'`."

Encoding: for every regular family, for large `X`, a collision pair `(n, n')` has
`σ(n) ≠ σ(n')` (so `A_3 ≥ 1` and the determinant in `Cite_LP_sieve37` is nonzero). -/
def Claim_SvSigmaDistinct : Prop :=
  ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℕ, S4a.SvDcond δ D →
    ∀ 𝒜 : ℝ → Finset ℕ, SV.RegularFamily D 𝒜 →
      ∃ X₀ : ℝ, ∀ X ≥ X₀, ∀ d n n' : ℕ, SV.CollisionPair D (𝒜 X) X d n n' → sig n ≠ sig n'

-- deps: Cite_LP_sieve37 (two-dimensional upper-bound sieve), Claim_SvSigmaDistinct (nonzero
--       determinant), Eq_SvCollision, Eq_SvTwoSided (S4a; λn' ≤ s(n') ≤ C_δ n'), S4a.A0Tuple
--       (nn' ≤ X^{14/15}, so T ≫_δ X^{1/15} and log T ≍ log X), linear Diophantine theory.
-- used by: Prop_SvSecondMoment (off-diagonal count).
/-- The sieve bound for a fixed collision pair, EP1054.tex lines 1588–1618 (unlabeled).
"For fixed `n,n'`, … every integral solution has the form `p=p_0+A_2t`, `p'=p'_0+A_1t` … All
relevant values of `t` lie in an interval of length at most `T:=Xdh/(n s(n'))` … The standard
two-dimensional upper-bound sieve, in the form used in [LP, (3.7)], therefore gives
`\ll_\delta \frac{Xdh}{nn'(\log X)^2}\frac{A_1}{\varphi(A_1)}\frac{A_2}{\varphi(A_2)}
\frac{A_3}{\varphi(A_3)}` possible prime pairs."

Encoding: `dh = SV.gcdS n n'`, `A_1 = s(n)/(dh)`, `A_2 = s(n')/(dh)`, `A_3 = SV.A3 n n'`; the count
is `SV.pairCount`. `C` is uniform in `X ≥ X₀`, `d` and the pair. -/
def Claim_SvSievePairs : Prop :=
  ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℕ, S4a.SvDcond δ D →
    ∀ 𝒜 : ℝ → Finset ℕ, SV.RegularFamily D 𝒜 →
      ∃ C : ℝ, ∃ X₀ : ℝ, ∀ X ≥ X₀, ∀ d n n' : ℕ, SV.CollisionPair D (𝒜 X) X d n n' →
        (SV.pairCount D (𝒜 X) X d n n' : ℝ) ≤
          C * (X * (SV.gcdS n n' : ℝ) / ((n : ℝ) * (n' : ℝ) * Real.log X ^ 2)) *
            SV.phiRatio (aliquot n / SV.gcdS n n') * SV.phiRatio (aliquot n' / SV.gcdS n n') *
            SV.phiRatio (SV.A3 n n')

-- deps: Std_totient_sigma (first inequality); monotonicity of σ(m)/m under divisibility
--       (Mathlib `Nat.abundancyIndex_le_of_dvd`, second). The paper's third inequality is
--       Eq_SvImageAbundancy.
-- used by: Prop_SvSecondMoment (A_1, A_2 factors, φ(h) ≫_δ h), Claim_SvA322Reduction (line 1735),
--          Eq_SvFSum and Eq_SvQRSum (φ(q₀h) ≫_δ q₀h, line 1789).
/-- `eq:sv-totient`, EP1054.tex lines 1620–1627.
"If `v\mid s(t)`, then `\frac v{\varphi(v)}\leq\zeta(2)\frac{\sigma(v)}v
\leq\zeta(2)\frac{\sigma(s(t))}{s(t)}\leq\zeta(2)B_\delta` (`t\in\{n,n'\}`)."

Encoding: the first two inequalities, for any `v ∣ m` with `v, m ≥ 1` (`m = s(t)`); the last one is
`Eq_SvImageAbundancy B_δ t`, supplied by `lem:sv-regular`. `ζ(2) = π²/6`. -/
def Eq_SvTotient : Prop :=
  ∀ v m : ℕ, 1 ≤ v → 1 ≤ m → v ∣ m →
    (v : ℝ) / (v.totient : ℝ) ≤ Real.pi ^ 2 / 6 * abundancy v ∧ abundancy v ≤ abundancy m

-- deps: Std_Mertens3 (A_{3,1}: ∏_{p≤(log log X)^2} p/(p−1) ≪ log log log X ≪ log Y);
--       Eq_SvTwoSided (S4a; A_3 ≪_δ X^{7/15}, so A_{3,3}/φ(A_{3,3}) ≪ 1); Eq_SvLP25 at n from
--       Lem_SvRegular (the primes removed from A_{3,2} divide σ(n) and exceed (log log X)^2).
-- used by: Prop_SvSecondMoment (reduction to eq:sv-reduced-collision-sum).
/-- The reduction of the `A_3` factor, EP1054.tex lines 1631–1646 (unlabeled).
"Let `A_{3,1}` contain its prime factors at most `(\log\log X)^2`, let `A_{3,2}` contain those in
`((\log\log X)^2,\log X]`, and let `A_{3,3}` contain those exceeding `\log X`. Since
`A_3\ll_\delta X^{7/15}`, `A_{3,1}/\varphi(A_{3,1})\ll\log Y`, `A_{3,3}/\varphi(A_{3,3})\ll1`. Let
`A'_{3,2}` be the largest divisor of `A_{3,2}` coprime to `\sigma(n)`. … (eq:sv-LP25) gives
`A_{3,2}/\varphi(A_{3,2})\ll A'_{3,2}/\varphi(A'_{3,2})`."

Encoding: the combined consequence `A_3/φ(A_3) ≤ C log Y · A'_{3,2}/φ(A'_{3,2})` for every
collision pair, `C` uniform in `X ≥ X₀`, `d` and the pair. All three bounds are written with an
**unsubscripted** `≪` (contrast `≪_δ` at lines 1612, 1653), so `C` is absolute and comes before
`∀ δ`; only `X₀` depends on `δ, D` and the family. (True: `∏_{p≤(log log X)^2} p/(p−1) ≍
log log log X ≍ log Y`; `A_3 ≤ C_δ X^{7/15}` has `O(log X/log log X)` prime factors above `log X`, so
`A_{3,3}/φ(A_{3,3}) → 1`; the removed primes satisfy `∏ p/(p−1) ≤ exp(2∑ 1/p) ≤ e^2` by
`eq:sv-LP25`.) -/
def Claim_SvA3Reduction : Prop :=
  ∃ C : ℝ, ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℕ, S4a.SvDcond δ D →
    ∀ 𝒜 : ℝ → Finset ℕ, SV.RegularFamily D 𝒜 →
      ∃ X₀ : ℝ, ∀ X ≥ X₀, ∀ d n n' : ℕ, SV.CollisionPair D (𝒜 X) X d n n' →
        SV.phiRatio (SV.A3 n n') ≤ C * Real.log (SV.Ycut X) * SV.ratio32 X n n'

-- deps: Claim_SvLargeH (h > X^{10/33}) and Claim_SvSmallH (h ≤ X^{10/33}); the split is additive.
-- used by: Prop_SvSecondMoment.
/-- `eq:sv-reduced-collision-sum`, EP1054.tex lines 1647–1657.
"Consequently, it remains to prove `\frac{X\log Y}{(\log X)^2}\sum_{n\ne n'}\frac{dh}{nn'}
\frac{A'_{3,2}}{\varphi(A'_{3,2})}\ll_\delta\frac{X}{d\log Y}`, where the sum is restricted to
pairs `n,n'` admitting an off-diagonal collision in (eq:sv-collision), and `dh=\gcd(s(n),s(n'))`."

Encoding: same quantifier shape as `Prop_SvSecondMoment` (uniformly for `d ∈ 𝒟_X`); the sum is
`SV.reducedCollisionSum … (fun _ => True)`. -/
def Eq_SvReducedCollisionSum : Prop :=
  ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℕ, S4a.SvDcond δ D →
    ∀ 𝒜 : ℝ → Finset ℕ, SV.RegularFamily D 𝒜 →
      ∀ c c₁ c₂ c₃ : ℝ, 0 < c → 0 < c₁ → 0 < c₂ → 0 < c₃ →
        ∃ C : ℝ, ∃ X₀ : ℝ, ∀ X ≥ X₀, ∀ 𝒟 : Finset ℕ, SV.ClassesAt (𝒜 X) X c c₁ c₂ c₃ 𝒟 →
          ∀ d ∈ 𝒟,
            X * Real.log (SV.Ycut X) / Real.log X ^ 2 *
                SV.reducedCollisionSum D (𝒜 X) X d (fun _ => True) ≤
              C * (X / ((d : ℝ) * Real.log (SV.Ycut X)))

-- deps: Lem_SvRegular ((i) at n and ℓ: gcd(n, σ(n)) = gcd(ℓ, σ(ℓ)) = d, d Y-smooth; (ii) at n:
--       every prime factor of s(n)/d, hence of h, exceeds y(n) ≥ Y), Eq_SvCollision
--       (s(n) = q s(ℓ) + σ(ℓ) with q ∤ ℓ, and σ(n) = (q+1)σ(ℓ)), S4a.A0Tuple (q > ℓ, q > Y).
-- used by: Claim_SvLargeHRigidity (q ≡ q' mod h once ℓ = ℓ'; s(ℓ) must be a unit mod h).
/-- The unit claim of the large-`h` case, EP1054.tex lines 1663–1676 (unlabeled).
"Suppose first that `h>X^{10/33}`. Write `n=q\ell` and `n'=q'\ell'`. We claim that
`\gcd(h,s(\ell)\sigma(\ell))=1`. … Thus both `s(\ell)` and `\sigma(\ell)` are units modulo `h`. It
follows that `q` is fixed in a reduced residue class modulo `h`, and the same holds for `q'`."

Encoding: for large `X`, two members `M = pqrk`, `M' = p'q'r'k'` of the same class `𝒜_d(X)` with
`n = qrk ≠ n' = q'r'k'`, `s(M) = s(M')` and `h = gcd(s(n), s(n'))/d > X^{10/33}` have
`gcd(h, s(ℓ)σ(ℓ)) = 1` and `gcd(h, s(ℓ')σ(ℓ')) = 1` (`ℓ = rk`, `ℓ' = r'k'`; the second is "the same
holds for `q'`", by the symmetric argument). The hypothesis `h > X^{10/33}` is the paper's setting
and is kept, although the argument does not use it. -/
def Claim_SvLargeHUnits : Prop :=
  ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℕ, S4a.SvDcond δ D →
    ∀ 𝒜 : ℝ → Finset ℕ, SV.RegularFamily D 𝒜 →
      ∃ X₀ : ℝ, ∀ X ≥ X₀, ∀ d p q r k p' q' r' k' : ℕ,
        SV.MemberTuple D (𝒜 X) X d p q r k → SV.MemberTuple D (𝒜 X) X d p' q' r' k' →
        q * r * k ≠ q' * r' * k' →
        aliquot (p * q * r * k) = aliquot (p' * q' * r' * k') →
        X ^ ((10 : ℝ) / 33) < ((SV.gcdS (q * r * k) (q' * r' * k') / d : ℕ) : ℝ) →
        Nat.Coprime (SV.gcdS (q * r * k) (q' * r' * k') / d) (aliquot (r * k) * sig (r * k)) ∧
          Nat.Coprime (SV.gcdS (q * r * k) (q' * r' * k') / d) (aliquot (r' * k') * sig (r' * k'))

-- deps: Eq_SvCollision (s(pn) = p s(n) + σ(n) at both members, so dh ∣ σ(n) − σ(n'); and
--       s(n) = q s(ℓ) + σ(ℓ), s(n') = q' s(ℓ') + σ(ℓ')); dh ∣ s(n), dh ∣ s(n') by definition, whence
--       n ≡ σ(n) ≡ σ(n') ≡ n' (mod h); S4a.A0Tuple (p > n, q > ℓ, so the identities apply).
--       Pure elimination: multiply qℓ ≡ q'ℓ' by s(ℓ)s(ℓ') — no unit hypothesis needed.
-- used by: Claim_SvLargeHRigidity.
/-- `eq:sv-large-h-congruence`, EP1054.tex lines 1677–1684.
"Moreover, `n\equiv\sigma(n)\equiv\sigma(n')\equiv n'\pmod h`. Eliminating `q,q'` gives
`s(\ell')\ell\sigma(\ell)-s(\ell)\ell'\sigma(\ell')\equiv0\pmod h`."

Encoding: same setting as `Claim_SvLargeHUnits` (`ℓ = rk`, `ℓ' = r'k'`,
`h = gcd(s(n), s(n'))/d > X^{10/33}`); the congruence is a divisibility in `ℤ`, where the left side
may be negative. -/
def Eq_SvLargeHCongruence : Prop :=
  ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℕ, S4a.SvDcond δ D →
    ∀ 𝒜 : ℝ → Finset ℕ, SV.RegularFamily D 𝒜 →
      ∃ X₀ : ℝ, ∀ X ≥ X₀, ∀ d p q r k p' q' r' k' : ℕ,
        SV.MemberTuple D (𝒜 X) X d p q r k → SV.MemberTuple D (𝒜 X) X d p' q' r' k' →
        q * r * k ≠ q' * r' * k' →
        aliquot (p * q * r * k) = aliquot (p' * q' * r' * k') →
        X ^ ((10 : ℝ) / 33) < ((SV.gcdS (q * r * k) (q' * r' * k') / d : ℕ) : ℝ) →
        ((SV.gcdS (q * r * k) (q' * r' * k') / d : ℕ) : ℤ) ∣
          (aliquot (r' * k') : ℤ) * ((r * k : ℕ) : ℤ) * (sig (r * k) : ℤ) -
            (aliquot (r * k) : ℤ) * ((r' * k' : ℕ) : ℤ) * (sig (r' * k') : ℤ)

-- deps: Eq_SvLargeHCongruence; Eq_SvTwoSided (S4a) and S4a.A0Tuple (ℓ ≤ X^{1/10}, so
--       |LHS of eq:sv-large-h-congruence| ≤ 2C_δ(C_δ+1)max(ℓ,ℓ')^3 ≪_δ X^{3/10} = o(X^{10/33}) < h,
--       hence it vanishes); Lem_SvRegular ((i)–(ii) at ℓ, ℓ': q₀^a ‖ d ⟹ q₀^a ‖ s(ℓ),
--       q₀^{a+1} ∣ σ(ℓ), whence gcd(ℓ², s(ℓ)) = d = gcd(ℓ'², s(ℓ'))); reduced denominators
--       (s(ℓ) = s(ℓ')), strict monotonicity of the quadratic (ℓ = ℓ'); then Claim_SvLargeHUnits
--       (s(ℓ) a unit mod h) with h ∣ s(n) = q s(ℓ) + σ(ℓ) and h ∣ s(n') = q' s(ℓ) + σ(ℓ) gives
--       h ∣ (q − q') s(ℓ), hence q ≡ q' (mod h).
-- used by: Claim_SvLargeH (both conjuncts: ℓ = ℓ' and q ≡ q' mod h, lines 1712, 1717–1718).
/-- The large-`h` rigidity, EP1054.tex lines 1663–1708 (unlabeled; the congruence
`eq:sv-large-h-congruence` is `Eq_SvLargeHCongruence`, the unit claim `Claim_SvLargeHUnits`).
"The absolute value of the left side is at most `2C_\delta(C_\delta+1)\max(\ell,\ell')^3\ll_\delta
X^{3/10}=o(X^{10/33})`, so it vanishes. … Thus `s(\ell)=s(\ell')`, and the displayed equality,
viewed as a strictly increasing quadratic in `\ell`, gives `\ell=\ell'`." With lines 1674–1676
("`q` is fixed in a reduced residue class modulo `h`, and the same holds for `q'`") and line 1717
("Because `\ell=\ell'`, the two primes belong to the same residue class modulo `h`").

Encoding: in the setting of `Claim_SvLargeHUnits`, `ℓ = rk = r'k' = ℓ'` **and** `q ≡ q' (mod h)`.
The congruence is part of the passage's content (it rests on `s(ℓ)` being a unit mod `h`, proved at
lines 1663–1676); `ℓ = ℓ'` alone does not imply it. -/
def Claim_SvLargeHRigidity : Prop :=
  ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℕ, S4a.SvDcond δ D →
    ∀ 𝒜 : ℝ → Finset ℕ, SV.RegularFamily D 𝒜 →
      ∃ X₀ : ℝ, ∀ X ≥ X₀, ∀ d p q r k p' q' r' k' : ℕ,
        SV.MemberTuple D (𝒜 X) X d p q r k → SV.MemberTuple D (𝒜 X) X d p' q' r' k' →
        q * r * k ≠ q' * r' * k' →
        aliquot (p * q * r * k) = aliquot (p' * q' * r' * k') →
        X ^ ((10 : ℝ) / 33) < ((SV.gcdS (q * r * k) (q' * r' * k') / d : ℕ) : ℝ) →
        r * k = r' * k' ∧ q ≡ q' [MOD (SV.gcdS (q * r * k) (q' * r' * k') / d)]

-- deps: Claim_SvLargeHRigidity (ℓ = ℓ' and q ≡ q' mod h), Std_divisorBound (τ(s(q'ℓ)) = X^{o(1)}),
--       Std_Mertens2 (A'_{3,2}/φ(A'_{3,2}) ≪ log log X/log Y; bounded ∑_{q'} 1/q'), S4a.A0Tuple
--       (∑_ℓ ℓ^{-2} ≪ X^{-1/15}), d ≤ Y^c = X^{o(1)}.
-- used by: Eq_SvReducedCollisionSum.
/-- The large-`h` contribution, EP1054.tex lines 1710–1731 (unlabeled).
"Summing the left side of (eq:sv-reduced-collision-sum) and using `\ell=\ell'` gives
`\ll\frac{Xd\log\log X}{(\log X)^2}\sum_{q,q',\ell,h}\frac{h}{qq'\ell^2}`. … The contribution is
therefore `dX^{14/15+o(1)}=o\!\left(\frac{X}{d\log Y}\right)`, uniformly for `d\leq Y^c`."

Encoding: the part of the reduced sum with `h > X^{10/33}`; `o(·)` = `∀ ε > 0, ∃ X₀`; uniform for
`Y`-smooth `1 ≤ d ≤ Y^c` (as the paper says), the threshold depending on `c` and `ε`. -/
def Claim_SvLargeH : Prop :=
  ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℕ, S4a.SvDcond δ D →
    ∀ 𝒜 : ℝ → Finset ℕ, SV.RegularFamily D 𝒜 →
      ∀ c : ℝ, 0 < c → ∀ ε : ℝ, 0 < ε → ∃ X₀ : ℝ, ∀ X ≥ X₀, ∀ d : ℕ,
        1 ≤ d → IsSmooth (SV.Ycut X) d → (d : ℝ) ≤ SV.Ycut X ^ c →
          X * Real.log (SV.Ycut X) / Real.log X ^ 2 *
              SV.reducedCollisionSum D (𝒜 X) X d (fun h => X ^ ((10 : ℝ) / 33) < (h : ℝ)) ≤
            ε * (X / ((d : ℝ) * Real.log (SV.Ycut X)))

/-! ### The small-`h` range (EP1054.tex lines 1733–1859) -/

namespace SV

/-- The residue-pair congruences of the small-`h` case, EP1054.tex lines 1749–1751 (with `n', h, k`
fixed): "`qrk\equiv(q+1)(r+1)\sigma(k)\equiv n'\pmod h`", for a candidate pair `(a, b)` in place of
`(q, r)`. (For a collision, `σ(n) = (q+1)(r+1)σ(k)` because `q`, `r`, `k` are pairwise coprime.) -/
def ResiduePair (h n' k a b : ℕ) : Prop :=
  a * b * k ≡ n' [MOD h] ∧ (a + 1) * (b + 1) * sig k ≡ n' [MOD h]

open Classical in
/-- `𝔣(qr)`, EP1054.tex lines 1763–1770 (`n', h, k` fixed; `q_0` prime):
"`\mathfrak{f}(qr)=\sum_{(\log\log X)^2<q_0\leq\log X,\ q_0\mid\sigma(kqr)-\sigma(n'),\
q_0\nmid h\sigma(kqr)}\frac1{q_0}`".
`σ(kqr)` is written `sig (q * r * k)` (the file's spelling `n = q * r * k`); the divisibility of the
difference is taken in `ℤ`. -/
noncomputable def frak (X : ℝ) (n' h k q r : ℕ) : ℝ :=
  ∑ q₀ ∈ (primesIoc ((logIt 2 X) ^ 2) (Real.log X)).filter
      (fun q₀ : ℕ => (q₀ : ℤ) ∣ (sig (q * r * k) : ℤ) - (sig n' : ℤ) ∧
        ¬ q₀ ∣ h * sig (q * r * k)),
    (1 : ℝ) / q₀

open Classical in
/-- `A''_{3,2}/φ(A''_{3,2})`, EP1054.tex lines 1733–1734: `A''_{3,2}` is the largest divisor of
`A'_{3,2}` coprime to `s(n')`. As for `ratio32`, encoded through `m/φ(m) = ∏_{p ∣ m} p/(p−1)`: the
product over primes `p ∣ A_3` in `((log log X)^2, log X]` with `p ∤ σ(n)` and `p ∤ s(n')`. -/
noncomputable def ratio322 (X : ℝ) (n n' : ℕ) : ℝ :=
  ∏ p ∈ (A3 n n').primeFactors.filter
      (fun p : ℕ => (logIt 2 X) ^ 2 < (p : ℝ) ∧ (p : ℝ) ≤ Real.log X ∧ ¬ p ∣ sig n ∧
        ¬ p ∣ aliquot n'),
    (p : ℝ) / ((p : ℝ) - 1)

/-- The primes `q ∈ (X^{7/20}, X^{11/30}]` with `q ≡ a (mod h)` (the `q`-range of
`eq:sv-factorization` in one residue class; EP1054.tex line 1798, "the sums are over the fixed
residue pair"). -/
noncomputable def qClass (X : ℝ) (h a : ℕ) : Finset ℕ :=
  (primesIoc (X ^ ((7 : ℝ) / 20)) (X ^ ((11 : ℝ) / 30))).filter (fun q : ℕ => q ≡ a [MOD h])

/-- The primes `r ∈ (X^{1/15}, X^{1/12}]` with `r ≡ b (mod h)`. -/
noncomputable def rClass (X : ℝ) (h b : ℕ) : Finset ℕ :=
  (primesIoc (X ^ ((1 : ℝ) / 15)) (X ^ ((1 : ℝ) / 12))).filter (fun r : ℕ => r ≡ b [MOD h])

end SV

-- deps: Eq_SvTotient (for v = the product of the removed primes, v ∣ s(n'):
--       v/φ(v) ≤ ζ(2)σ(v)/v ≤ ζ(2)σ(s(n'))/s(n')) with Eq_SvImageAbundancy at n' (≤ ζ(2)B_δ; from
--       SV.RegularFamily, via the member whose n-part is n'); each factor p/(p−1) ≥ 1.
-- used by: Claim_SvSmallH.
/-- The reduction `A'_{3,2} → A''_{3,2}`, EP1054.tex lines 1733–1739 (unlabeled).
"It remains to treat `h\leq X^{10/33}`. Let `A''_{3,2}` be the largest divisor of `A'_{3,2}`
coprime to `s(n')`. Equation (eq:sv-totient) gives
`\frac{A'_{3,2}}{\varphi(A'_{3,2})}\ll_\delta\frac{A''_{3,2}}{\varphi(A''_{3,2})}`."

Encoding: `SV.ratio32 X n n' ≤ C · SV.ratio322 X n n'` for every collision pair with
`h = gcd(s(n), s(n'))/d ≤ X^{10/33}` (the paper's range; the argument does not use it). `≪_δ`: `C`
comes after `∀ δ, D, 𝒜`, uniform in `X ≥ X₀`, `d` and the pair. -/
def Claim_SvA322Reduction : Prop :=
  ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℕ, S4a.SvDcond δ D →
    ∀ 𝒜 : ℝ → Finset ℕ, SV.RegularFamily D 𝒜 →
      ∃ C : ℝ, ∃ X₀ : ℝ, ∀ X ≥ X₀, ∀ d n n' : ℕ, SV.CollisionPair D (𝒜 X) X d n n' →
        ((SV.gcdS n n' / d : ℕ) : ℝ) ≤ X ^ ((10 : ℝ) / 33) →
        SV.ratio32 X n n' ≤ C * SV.ratio322 X n n'

-- deps: Lem_SvRegular (its square-divisibility exclusion at n; every prime factor of h exceeds
--       y(n)), S4a.A0Tuple (n > X^{17/40}).
-- used by: Claim_SvSmallH (to apply Claim_SvResiduePairCount, line 1758); the `Squarefree h`
--          hypothesis of Eq_SvFSum and Eq_SvQRSum.
/-- Squarefreeness of small `h`, EP1054.tex lines 1740–1747 (unlabeled).
"We first note that `h` is squarefree in this range. Indeed, if `q_0^2\mid h`, then
`q_0^2\mid s(n)` and `q_0>y(n)`. By Lemma LP-inputs, this forces `q_0>n^{10/27}`. Since
`n>X^{17/40}`, `q_0^2>n^{20/27}>X^{17/54}>X^{10/33}\geq h`, a contradiction."

Encoding: for large `X`, every collision pair with `h = gcd(s(n), s(n'))/d ≤ X^{10/33}` has `h`
squarefree. -/
def Claim_SvSmallHSquarefree : Prop :=
  ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℕ, S4a.SvDcond δ D →
    ∀ 𝒜 : ℝ → Finset ℕ, SV.RegularFamily D 𝒜 →
      ∃ X₀ : ℝ, ∀ X ≥ X₀, ∀ d n n' : ℕ, SV.CollisionPair D (𝒜 X) X d n n' →
        ((SV.gcdS n n' / d : ℕ) : ℝ) ≤ X ^ ((10 : ℝ) / 33) → Squarefree (SV.gcdS n n' / d)

-- deps: Lem_SvRegular ((i) at n: gcd(n, σ(n)) = d, d Y-smooth; (ii) at n: every prime factor of
--       s(n)/d — hence of h — exceeds y(n) ≥ Y; (i) at n': d ∣ s(n')), Eq_SvCollision (dh ∣
--       σ(n) − σ(n'); with dh ∣ s(n), dh ∣ s(n') this gives qrk = n ≡ σ(n) ≡ σ(n') ≡ n' mod h),
--       S4a.A0Tuple (k < r < q, so σ(n) = (q+1)(r+1)σ(k)).
-- used by: Claim_SvSmallH (with Claim_SvResiduePairCount: for fixed n', h, k the collisions'
--          (q, r) lie in at most τ(h) residue pairs).
/-- The residue congruences of the small-`h` case, EP1054.tex lines 1749–1758 (unlabeled).
"Fix `n',h,k`. The congruences `qrk\equiv(q+1)(r+1)\sigma(k)\equiv n'\pmod h` may therefore be
solved for the required symmetric functions. Indeed, any prime dividing both `h` and either `n` or
`\sigma(n)` would divide `\gcd(n,\sigma(n))=d`, which is impossible because every prime factor of
`h` exceeds `Y`. Thus `k` and `\sigma(k)` are units modulo `h`."

Encoding: for large `X`, if `M = pqrk ∈ 𝒜_d(X)` and its `n`-part `n = qrk` forms a collision pair
with `n'` whose `h = gcd(s(n), s(n'))/d ≤ X^{10/33}`, then `k` and `σ(k)` are coprime to `h` and
`(q, r)` satisfies `SV.ResiduePair h n' k`. -/
def Claim_SvSmallHResidues : Prop :=
  ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℕ, S4a.SvDcond δ D →
    ∀ 𝒜 : ℝ → Finset ℕ, SV.RegularFamily D 𝒜 →
      ∃ X₀ : ℝ, ∀ X ≥ X₀, ∀ d p q r k n' : ℕ, SV.MemberTuple D (𝒜 X) X d p q r k →
        SV.CollisionPair D (𝒜 X) X d (q * r * k) n' →
        ((SV.gcdS (q * r * k) n' / d : ℕ) : ℝ) ≤ X ^ ((10 : ℝ) / 33) →
        Nat.Coprime k (SV.gcdS (q * r * k) n' / d) ∧
          Nat.Coprime (sig k) (SV.gcdS (q * r * k) n' / d) ∧
          SV.ResiduePair (SV.gcdS (q * r * k) n' / d) n' k q r

-- deps: elementary — CRT over the prime factors of the squarefree h; modulo a prime ℓ₀ ∣ h the
--       congruences give ab ≡ n'k⁻¹ and a + b ≡ n'σ(k)⁻¹ − n'k⁻¹ − 1, so a is a root of a monic
--       quadratic over ZMod ℓ₀ (≤ 2 roots) and b is determined by a; 2^{ω(h)} = τ(h) for squarefree h.
-- used by: Claim_SvSmallH (the factor τ(h), lines 1758–1762, 1833).
open Classical in
/-- The residue-pair count, EP1054.tex lines 1756–1762 (unlabeled).
"The two congruences therefore determine `qr` and `q+r` modulo `h`. Since `h` is squarefree, there
are at most `\tau(h)` possible ordered residue pairs `q\equiv a\pmod h`, `r\equiv b\pmod h`."

Encoding: the finite fact behind the sentence, with the two hypotheses the paper names (`h`
squarefree; `k`, `σ(k)` units mod `h`, supplied by `Claim_SvSmallHResidues`): the ordered pairs
`(a, b) ∈ [0, h)^2` satisfying `SV.ResiduePair h n' k a b` number at most `τ(h)`. -/
def Claim_SvResiduePairCount : Prop :=
  ∀ h n' k : ℕ, Squarefree h → Nat.Coprime k h → Nat.Coprime (sig k) h →
    ((Finset.range h ×ˢ Finset.range h).filter
        (fun ab : ℕ × ℕ => SV.ResiduePair h n' k ab.1 ab.2)).card ≤ h.divisors.card

-- deps: Std_Mertens2 (case 𝔣 > 1: ∏_{(log log X)^2<p≤log X} p/(p−1) ≪ log log X/log log log X
--       ≪ log log X/log Y); ∏ p/(p−1) ≤ exp(2∑ 1/p) (case 𝔣 ≤ 1); every prime of A''_{3,2} occurs
--       in 𝔣(qr): p ∣ A_3 ∣ σ(n) − σ(n'), p ∤ σ(n), and p ∤ s(n') forces p ∤ h (h ∣ s(n')).
-- used by: Claim_SvSmallH (it turns the A''-ratio into the summand of Eq_SvQRSum).
/-- `eq:sv-intermediate-totient`, EP1054.tex lines 1763–1778.
"For one such pair put `\mathfrak{f}(qr)=…`, where `q_0` is prime. Mertens' theorem gives
`\frac{A''_{3,2}}{\varphi(A''_{3,2})}\ll_\delta1+\frac{\log\log X}{\log Y}\mathfrak{f}(qr)`.
Indeed, when `\mathfrak{f}(qr)\leq1`, the logarithm of the left side is `O(\mathfrak{f}(qr))`.
When `\mathfrak{f}(qr)>1`, Mertens' theorem bounds the contribution of the full prime range by
`O(\log\log X/\log Y)`."

Encoding: in the setting of `Claim_SvSmallHResidues` (`n = qrk` the `n`-part of a member of
`𝒜_d(X)`, `(n, n')` a collision pair, `h = gcd(s(n), s(n'))/d ≤ X^{10/33}`),
`SV.ratio322 X n n' ≤ C (1 + (log log X/log Y) 𝔣(qr))` with `𝔣(qr) = SV.frak X n' h k q r`.
`≪_δ`: `C` after `∀ δ, D, 𝒜`, uniform in `X ≥ X₀` and the data. -/
def Eq_SvIntermediateTotient : Prop :=
  ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℕ, S4a.SvDcond δ D →
    ∀ 𝒜 : ℝ → Finset ℕ, SV.RegularFamily D 𝒜 →
      ∃ C : ℝ, ∃ X₀ : ℝ, ∀ X ≥ X₀, ∀ d p q r k n' : ℕ, SV.MemberTuple D (𝒜 X) X d p q r k →
        SV.CollisionPair D (𝒜 X) X d (q * r * k) n' →
        ((SV.gcdS (q * r * k) n' / d : ℕ) : ℝ) ≤ X ^ ((10 : ℝ) / 33) →
        SV.ratio322 X (q * r * k) n' ≤
          C * (1 + logIt 2 X / Real.log (SV.Ycut X) *
            SV.frak X n' (SV.gcdS (q * r * k) n' / d) k q r)

-- deps: Std_BrunTitchmarsh with partial summation (q in its reduced class mod q₀h, where
--       q₀h ≤ X^{10/33} log X < X^{7/20−ε₀}; r in its class mod h when h ≤ X^{1/20});
--       Eq_SvTotient with Eq_SvImageAbundancy at n' (h ∣ s(n'), so φ(q₀h) = (q₀−1)φ(h) ≫_δ q₀h);
--       ∑_{q₀>(log log X)^2} q₀^{-2} ≪ (log log X)^{-2}; the trivial count of r ≡ b (mod h) when
--       h > X^{1/20}. Uses: q > X^{7/20} > log X ≥ q₀ (a nonreduced class mod q₀ holds no
--       admissible q), k < r < q (σ(qrk) = (q+1)σ(rk)), q₀ ∤ σ(qrk) ⟹ σ(rk) invertible mod q₀.
-- used by: Eq_SvQRSum.
/-- `eq:sv-f-sum`, EP1054.tex lines 1780–1815.
"For fixed `n',h,k,r` and a prime `q_0` occurring in `\mathfrak{f}(qr)`, the congruence
`(q+1)\sigma(kr)\equiv\sigma(n')\pmod{q_0}` fixes `q` modulo `q_0`. … Brun--Titchmarsh and partial
summation, followed by (eq:sv-totient), give
`\sum_{q,r}\frac{\mathfrak{f}(qr)}{qr}\ll_\delta\begin{cases}\dfrac{\log X}{hX^{1/20}},&X^{1/20}<h
\leq X^{10/33},\\\dfrac{1}{h^2(\log\log X)^2},&h\leq X^{1/20}.\end{cases}` Here the sums are over
the fixed residue pair."

Encoding: "fixed `n', h, k`" and "the fixed residue pair": `n'` is the `n`-part of a member of
`𝒜_d(X)`; `h ∣ s(n')/d` (as `h = gcd(s(n), s(n'))/d` does), squarefree (`Claim_SvSmallHSquarefree`),
`h ≤ X^{10/33}`; `k ∈ SV.kSet X d`; `(a, b)` a residue pair (`SV.ResiduePair h n' k a b`). The sums
run over **all** primes of the two ranges in the classes `a`, `b` mod `h` (`SV.qClass`,
`SV.rClass`), an upper bound for the collisions. The two cases are two implications. `≪_δ`: `C`
after `∀ δ, D, 𝒜`, uniform in `X ≥ X₀`, `d, n', h, k, a, b`. -/
def Eq_SvFSum : Prop :=
  ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℕ, S4a.SvDcond δ D →
    ∀ 𝒜 : ℝ → Finset ℕ, SV.RegularFamily D 𝒜 →
      ∃ C : ℝ, ∃ X₀ : ℝ, ∀ X ≥ X₀, ∀ d n' h k a b : ℕ, (∃ p' : ℕ, SV.IsNPart D (𝒜 X) X d p' n') →
        h ∣ aliquot n' / d → Squarefree h → (h : ℝ) ≤ X ^ ((10 : ℝ) / 33) → k ∈ SV.kSet X d →
        SV.ResiduePair h n' k a b →
        (X ^ ((1 : ℝ) / 20) < (h : ℝ) →
            ∑ q ∈ SV.qClass X h a, ∑ r ∈ SV.rClass X h b,
                SV.frak X n' h k q r / ((q : ℝ) * (r : ℝ)) ≤
              C * (Real.log X / ((h : ℝ) * X ^ ((1 : ℝ) / 20)))) ∧
          ((h : ℝ) ≤ X ^ ((1 : ℝ) / 20) →
            ∑ q ∈ SV.qClass X h a, ∑ r ∈ SV.rClass X h b,
                SV.frak X n' h k q r / ((q : ℝ) * (r : ℝ)) ≤
              C * (1 / ((h : ℝ) ^ 2 * logIt 2 X ^ 2)))

-- deps: Eq_SvFSum (the 𝔣 part); Std_BrunTitchmarsh with partial summation and Eq_SvTotient (the
--       1/(qr) part: ∑_{q≡a} 1/q ≪_δ 1/φ(h) ≪_δ 1/h, and the r-sum bounds of Eq_SvFSum);
--       log log X ≥ log Y for large X. (eq:sv-intermediate-totient only motivates the summand; it
--       is applied in Claim_SvSmallH, not here.)
-- used by: Claim_SvSmallH (lines 1829–1850).
/-- `eq:sv-qr-sum`, EP1054.tex lines 1816–1827.
"The same progression bounds without `\mathfrak{f}` and (eq:sv-intermediate-totient) yield
`\sum_{q,r}\left(\frac1{qr}+\frac{\log\log X}{\log Y}\frac{\mathfrak{f}(qr)}{qr}\right)\ll_\delta
\begin{cases}\dfrac{(\log X)(\log\log X)}{hX^{1/20}\log Y},&X^{1/20}<h\leq X^{10/33},\\[6pt]
h^{-2},&h\leq X^{1/20}.\end{cases}`"

Encoding: the setting, sums and quantifier shape of `Eq_SvFSum`; the summand is the right side of
`eq:sv-intermediate-totient` divided by `qr`. -/
def Eq_SvQRSum : Prop :=
  ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℕ, S4a.SvDcond δ D →
    ∀ 𝒜 : ℝ → Finset ℕ, SV.RegularFamily D 𝒜 →
      ∃ C : ℝ, ∃ X₀ : ℝ, ∀ X ≥ X₀, ∀ d n' h k a b : ℕ, (∃ p' : ℕ, SV.IsNPart D (𝒜 X) X d p' n') →
        h ∣ aliquot n' / d → Squarefree h → (h : ℝ) ≤ X ^ ((10 : ℝ) / 33) → k ∈ SV.kSet X d →
        SV.ResiduePair h n' k a b →
        (X ^ ((1 : ℝ) / 20) < (h : ℝ) →
            ∑ q ∈ SV.qClass X h a, ∑ r ∈ SV.rClass X h b,
                (1 / ((q : ℝ) * (r : ℝ)) + logIt 2 X / Real.log (SV.Ycut X) *
                  (SV.frak X n' h k q r / ((q : ℝ) * (r : ℝ)))) ≤
              C * (Real.log X * logIt 2 X /
                ((h : ℝ) * X ^ ((1 : ℝ) / 20) * Real.log (SV.Ycut X)))) ∧
          ((h : ℝ) ≤ X ^ ((1 : ℝ) / 20) →
            ∑ q ∈ SV.qClass X h a, ∑ r ∈ SV.rClass X h b,
                (1 / ((q : ℝ) * (r : ℝ)) + logIt 2 X / Real.log (SV.Ycut X) *
                  (SV.frak X n' h k q r / ((q : ℝ) * (r : ℝ)))) ≤
              C * (1 / (h : ℝ) ^ 2))

-- deps: Claim_SvA322Reduction (A'_{3,2} → A''_{3,2}); Claim_SvSmallHSquarefree;
--       Claim_SvSmallHResidues and Claim_SvResiduePairCount (for fixed n', h, k the collisions'
--       (q, r) lie in at most τ(h) residue pairs mod h); Eq_SvIntermediateTotient (the A''-ratio is
--       ≤ C(1 + (log log X/log Y)𝔣(qr))); Eq_SvQRSum (the (q, r)-sum in one pair); Eq_SvKReciprocal
--       (the k-sum); Std_divisorBound (∑_{h∣s(n')} τ(h) ≤ τ(s(n'))^2 = X^{o(1)});
--       Eq_SvImageAbundancy (∑_{h∣s(n')} τ(h)/h ≤ (σ(s(n'))/s(n'))^2 ≤ B_δ^2); Eq_SvMReciprocal
--       (the n'-sum); d ≤ Y^c = X^{o(1)} (from SV.ClassesAt).
-- used by: Eq_SvReducedCollisionSum.
/-- The small-`h` contribution, EP1054.tex lines 1733–1859 (unlabeled).
"It remains to treat `h\leq X^{10/33}`. … For `X^{1/20}<h\leq X^{10/33}` … the total is
`X^{19/20+o(1)}/d=o(X/(d\log Y))`. For `h\leq X^{1/20}` the fixed-`n',h` contribution is
`\ll_\delta\frac{X}{\log X}\frac{\tau(h)}{hn'}`. … Summing over `h` and then using
(eq:sv-m-reciprocal) gives `O_\delta(X/(d\log Y))`."

Encoding: the part of the reduced sum with `h ≤ X^{10/33}` is `≪_δ X/(d log Y)`, with the
quantifier shape of `Prop_SvSecondMoment` (uniformly for `d ∈ 𝒟_X`). -/
def Claim_SvSmallH : Prop :=
  ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℕ, S4a.SvDcond δ D →
    ∀ 𝒜 : ℝ → Finset ℕ, SV.RegularFamily D 𝒜 →
      ∀ c c₁ c₂ c₃ : ℝ, 0 < c → 0 < c₁ → 0 < c₂ → 0 < c₃ →
        ∃ C : ℝ, ∃ X₀ : ℝ, ∀ X ≥ X₀, ∀ 𝒟 : Finset ℕ, SV.ClassesAt (𝒜 X) X c c₁ c₂ c₃ 𝒟 →
          ∀ d ∈ 𝒟,
            X * Real.log (SV.Ycut X) / Real.log X ^ 2 *
                SV.reducedCollisionSum D (𝒜 X) X d (fun h => (h : ℝ) ≤ X ^ ((10 : ℝ) / 33)) ≤
              C * (X / ((d : ℝ) * Real.log (SV.Ycut X)))

/-! ## The proof of Theorem `thm:small-values` (EP1054.tex lines 1862–1884) -/

-- deps: Cauchy–Schwarz (Mathlib `Finset.sum_mul_sq_le_sq_mul_sq`); ∑_u R(u) = #S.
-- used by: Claim_SvClassImage.
/-- Cauchy–Schwarz for an image, EP1054.tex lines 1863–1868 (unlabeled).
"For each `d\in\mathcal{D}_X`, Cauchy–Schwarz … give
`\#s(\mathcal{A}_d(X))\geq\frac{\#\mathcal{A}_d(X)^2}{\sum_uR_d(u)^2}`."

Encoding: the general finite fact, cross-multiplied (no division by zero): for a finset `S` and a
map `s`, `(#S)^2 ≤ #s(S) · ∑_{u ∈ s(S)} #{M ∈ S : s(M) = u}^2`. -/
def Claim_SvCauchySchwarz : Prop :=
  ∀ (S : Finset ℕ) (s : ℕ → ℕ),
    ((S.card : ℕ) : ℝ) ^ 2 ≤
      ((S.image s).card : ℝ) * ∑ u ∈ S.image s, (((S.filter (fun M => s M = u)).card : ℕ) : ℝ) ^ 2

-- deps: Claim_SvCauchySchwarz, Lem_SvClasses (lower bound in eq:sv-class-size, via SV.ClassesAt),
--       Prop_SvSecondMoment.
-- used by: Claim_SvImageCount.
/-- The per-class image bound, EP1054.tex lines 1863–1869 (unlabeled).
"For each `d\in\mathcal{D}_X`, Cauchy–Schwarz, Lemma sv-classes, and Proposition sv-second-moment
give `\#s(\mathcal{A}_d(X))\geq\frac{\#\mathcal{A}_d(X)^2}{\sum_uR_d(u)^2}\gg_\delta
\frac{X}{d\log Y}`."

Encoding: quantifier shape of `Prop_SvSecondMoment`; `c' > 0` is the `≫_δ` constant. -/
def Claim_SvClassImage : Prop :=
  ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℕ, S4a.SvDcond δ D →
    ∀ 𝒜 : ℝ → Finset ℕ, SV.RegularFamily D 𝒜 →
      ∀ c c₁ c₂ c₃ : ℝ, 0 < c → 0 < c₁ → 0 < c₂ → 0 < c₃ →
        ∃ c' : ℝ, 0 < c' ∧ ∃ X₀ : ℝ, ∀ X ≥ X₀, ∀ 𝒟 : Finset ℕ,
          SV.ClassesAt (𝒜 X) X c c₁ c₂ c₃ 𝒟 →
            ∀ d ∈ 𝒟, c' * (X / ((d : ℝ) * Real.log (SV.Ycut X))) ≤
              (((SV.classFin (𝒜 X) X d).image aliquot).card : ℝ)

-- deps: Lem_SvClasses (a class set 𝒟_X with disjoint images and ∑ 1/d ≫_δ log Y),
--       Claim_SvClassImage; s(𝒜_d(X)) ⊆ s(𝒜(X)).
-- used by: SvFamilyTarget (S4a; the construction target of lines 1217–1222), with Claim_SvWitness.
/-- The image count, EP1054.tex lines 1870–1876 (unlabeled).
"The image sets are disjoint, and hence `\#s(\mathcal{A}(X))\gg_\delta\frac{X}{\log Y}
\sum_{d\in\mathcal{D}_X}\frac1d\gg_\delta X`."

Encoding: for every regular family, `#s(𝒜(X)) ≥ c X` for `X ≥ X₀`. -/
def Claim_SvImageCount : Prop :=
  ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℕ, S4a.SvDcond δ D →
    ∀ 𝒜 : ℝ → Finset ℕ, SV.RegularFamily D 𝒜 →
      ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℝ, ∀ X ≥ X₀, c * X ≤ (((𝒜 X).image aliquot).card : ℝ)

-- deps: Eq_SvBasic (S4a; f(s(n)) ≤ n and s(n) ∈ 𝓡 for n ≥ 2), Eq_SvTwoSided (S4a) at t = M
--       (λ < s(M)/M < C_δ); 𝒜(X) ⊆ 𝒜_0(X) ⊆ [1, X].
-- used by: SvFamilyTarget (S4a; with Claim_SvImageCount), then thm:small-values by rescaling.
/-- The witness bounds, EP1054.tex lines 1877–1882 (unlabeled).
"If `N=s(M)` with `M\in\mathcal{A}(X)`, then (eq:sv-basic) and (eq:sv-two-sided) give
`f(N)\leq M<\delta N`. Moreover, `N=s(M)<C_\delta M\leq C_\delta X`."

Encoding: `N ∈ 𝓡` is made explicit (`f` has junk value `0` off `𝓡`); `C > 0` is `C_δ`, fixed
before `X`. With `Claim_SvImageCount` this is S4a's `SvFamilyTarget` for `𝒜(X)`, and "Replacing `X`
by `X/C_\delta` proves the theorem for `0<\delta\leq1`, and the case `\delta>1` follows from
`\delta=1`" (lines 1882–1883) is the spine's rescaling step. -/
def Claim_SvWitness : Prop :=
  ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ D : ℕ, S4a.SvDcond δ D →
    ∀ 𝒜 : ℝ → Finset ℕ, SV.RegularFamily D 𝒜 →
      ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℝ, ∀ X ≥ X₀, ∀ M ∈ 𝒜 X,
        aliquot M ∈ R ∧ f (aliquot M) ≤ M ∧ (M : ℝ) < δ * (aliquot M : ℝ) ∧
          (aliquot M : ℝ) < C * X

end Principia.Erdos1054
