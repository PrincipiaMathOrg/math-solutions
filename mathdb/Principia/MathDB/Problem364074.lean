/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.

# MathDB #364074 — the rank-difference conjecture (the reduction and the spine)

MathDB open problem #364074: with `p(n)` the partition function, `N(0,n)` the number of
partitions of `n` of Dyson rank zero, and `u(m,n)` the number of strongly unimodal sequences
of weight `n` and rank `m`,

  `u(0,n) − u(1,n) ≥ N(0,n)/2`   for every `n ≥ 8`.                                      (1)

## What this file is, and is not

The campaign write-up proves (1) by an effective circle-method argument: a false-theta kernel,
an order-16 Euler–Boole expansion with certified remainders, Dedekind eta inversion, a saddle
point, and a 220-bit Arb interval computation — plus an exact check of every `n` from `8` to
`10000`.  **That is a long project, not an impossible one** — an earlier version of this header
said "none of that is formalizable here", which conflated the two and was wrong.  The repo
already carries ~95 circle-method bricks from the Erdős 1054 / almost-all-Goldbach work
(`coeffModel_as_integral`, `coeffModel_eq_arc`, `arcs_disjoint`, `sum_setIntegral_disjoint`,
Bessel-on-a-set, Farey anchors, `e x = exp (2*pi*I*x)` with `integral_e_int`), so the
coefficient-extraction scaffolding transfers.  What does not transfer is the partition-specific
analysis: Dedekind eta inversion, the false-theta kernel, the saddle point, and Arb
certification.  The `10⁴`-term exact check remains genuinely hard, since `native_decide` would
introduce `ofReduceBool`, which this project's gate rejects outright.

What *is* exactly formalizable is the source's own **first reduction**, and it is not a
triviality of presentation — it is the step that converts a statement about three different
counting functions into a statement about one.  Everything analytic downstream is about `Eₙ`
alone, and that is only legitimate because of `rank_difference_iff`.

## The reduction

The source quotes the identity

  `u(0,n) + u(1,n) = (p(n) + N(0,n))/2`                                                  (2)

and asserts that (1) is *equivalent* to `Eₙ := p(n) − 4u(1,n) ≥ 0`.  Written over `ℤ` with the
denominator cleared, that equivalence is exact arithmetic and is proved here in **both**
directions — the source needs only `⟸`, but the converse costs nothing and records that no
strength was lost at the reduction, which is precisely the kind of gap prose cannot see.

## The spine

`rank_difference_of_split` composes the reduction with the two obligations the write-up
discharges analytically, each named as a hypothesis rather than assumed:

* `ExactRange` — `Eₙ ≥ 0` for `8 ≤ n ≤ 10000`, the Arb-certified finite check;
* `AnalyticRange` — `Eₙ ≥ 0` for `n ≥ 10000`, the major-arc estimate.

Neither is proved and neither is an axiom, so the file certifies the implication only and its
footprint stays clean.  **The overlap at `n = 10000` is deliberate in the source and is
preserved here**: the two hypotheses are stated with `≤` and `≥` at the same endpoint, so the
composition cannot fall through a gap between them — which is exactly the sort of off-by-one a
prose proof states and never checks.
-/
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.List.Chain

namespace Principia.MathDB.P364074

/-- **The first reduction, exactly.**  Given the source's identity (2) with the denominator
cleared — `2(u₀ + u₁) = p + N` — the target `N ≤ 2(u₀ − u₁)` is *equivalent* to `4u₁ ≤ p`.

Both directions are proved.  The source uses only `⟸`; the converse is free and records that
the reduction loses no strength, which is the failure a prose proof cannot exhibit. -/
theorem rank_difference_iff {p N u0 u1 : ℤ} (h : 2 * (u0 + u1) = p + N) :
    N ≤ 2 * (u0 - u1) ↔ 4 * u1 ≤ p := by
  constructor
  · intro h1
    linarith
  · intro h1
    linarith

/-- The Arb-certified finite check: `Eₙ ≥ 0` for `8 ≤ n ≤ 10000`. -/
-- SPEC-CARRY-CHECKED: ExactRange -- 2026-09-26.  Blocked for a reason verified in Mathlib rather
-- than assumed: there is NO computable characterisation of `p(n)`.
-- `Mathlib/Combinatorics/Enumerative/Partition/GenFun.lean` proves the general product formula
-- and marks the specialisation to `p(n)` as its own `(TODO: prove this)` at line 26 -- so there
-- is nothing to evaluate at `n = 10000` and kernel speed never enters.  An uncounted row.
def ExactRange (E : ℕ → ℤ) : Prop := ∀ n : ℕ, 8 ≤ n → n ≤ 10000 → 0 ≤ E n

/-- The major-arc estimate: `Eₙ ≥ 0` for every `n ≥ 10000`. -/
-- SPEC-CARRY-CHECKED: AnalyticRange -- 2026-09-26.  Effective circle-method asymptotics (the
-- Euler-Boole expansion, certified remainders, the saddle point, interval arithmetic), none of
-- which Mathlib has.  A deliberate carry on an uncounted row; see `ExactRange` above.
def AnalyticRange (E : ℕ → ℤ) : Prop := ∀ n : ℕ, 10000 ≤ n → 0 ≤ E n

/-- **The two ranges cover `n ≥ 8`.**  Stated separately from the composition because this is
where the source's "the overlap is deliberate" is actually cashed: the endpoint `10000` belongs
to both hypotheses, so no `n` escapes.  Had the write-up's ranges been `≤ 10000` and `> 10000`
this would still hold; had they been `< 10000` and `> 10000` it would not, and nothing in the
prose would have shown it. -/
theorem nonneg_of_split {E : ℕ → ℤ} (hex : ExactRange E) (han : AnalyticRange E) :
    ∀ n : ℕ, 8 ≤ n → 0 ≤ E n := by
  intro n hn
  rcases le_or_gt n 10000 with h | h
  · exact hex n hn h
  · exact han n (le_of_lt h)

/-- **#364074, the spine.**  From the source's identity (2), the finite check and the major-arc
estimate, the rank-difference conjecture follows for every `n ≥ 8`.

The proof is the reduction applied pointwise; there is no mathematics in the composition, which
is the point.  What the analytic work still owes is exactly `ExactRange` and `AnalyticRange` for
the specific `E n = p n − 4 · u₁ n`. -/
theorem rank_difference_of_split {p N u0 u1 E : ℕ → ℤ}
    (hE : ∀ n : ℕ, E n = p n - 4 * u1 n)
    (hid : ∀ n : ℕ, 2 * (u0 n + u1 n) = p n + N n)
    (hex : ExactRange E) (han : AnalyticRange E) :
    ∀ n : ℕ, 8 ≤ n → N n ≤ 2 * (u0 n - u1 n) := by
  intro n hn
  have hnn : 0 ≤ E n := nonneg_of_split hex han n hn
  rw [hE n] at hnn
  exact (rank_difference_iff (hid n)).mpr (by linarith)

/-! ### The false-theta reindexing, exactly

The write-up passes from the false-theta sum (7) to the quadratic form (9) in one sentence:
"writing `r = a+b` and `j = a` in (7)".  That step is pure algebra and can be pinned down now,
independently of any analysis.

(7) sums `q^(T_r + j*r)` over `r >= 1`, `0 <= j <= r`, with `T_r = r(r+1)/2` the triangular number.
Substituting `r = a+b`, `j = a` reparametrises that index set by `a, b >= 0` with `a + b >= 1`, and
the exponent becomes

  `T_(a+b) + a(a+b) = (3/2)a^2 + 2ab + (1/2)b^2 + (a+b)/2 = Q(a,b)`,

which is (9)'s quadratic form.  **Doubled to stay in `Z`** -- the same denominator-clearing used
throughout this campaign -- the identity is `2Q(a,b) = (a+b)(3a + b + 1)`, and it factors, which
makes positivity immediate rather than a discriminant argument.

What this does NOT do is the analysis: the Euler-Boole expansion, the certified remainders, the
saddle point and the Arb interval arithmetic are all still owed, as is the bijectivity of the
reindexing as a statement about sums.  But the exponent identity underneath is now exact, and it
is the piece a formalisation would otherwise carry as an unchecked assumption.

**The bijectivity of the reindexing is no longer owed either (2026-09-25).**  `sum_reindex`
is the `(7) -> (9)` reparametrisation AS A STATEMENT ABOUT SUMS, for an arbitrary summand and
every truncation `a + b <= N`, and `endpoints_pentagonal` is the `(5) -> (6)` endpoint step.
What is still owed is the analysis alone: the Euler-Boole expansion, the certified
remainders, the saddle point and the Arb interval arithmetic, i.e. `ExactRange` and
`AnalyticRange`. -/

/-- Twice the `r`-th triangular number, kept integral. -/
def twoTri (r : ℤ) : ℤ := r * (r + 1)

/-- Twice the quadratic form `Q(a,b) = (3/2)a^2 + 2ab + (1/2)b^2 + (a+b)/2` of (9). -/
def twoQ (a b : ℤ) : ℤ := 3 * a ^ 2 + 4 * a * b + b ^ 2 + a + b

/-- **The reindexing identity.**  `r = a+b`, `j = a` sends the exponent `T_r + j*r` of (7) to
`Q(a,b)` of (9). -/
theorem twoQ_eq_twoTri_add (a b : ℤ) :
    twoQ a b = twoTri (a + b) + 2 * a * (a + b) := by
  simp only [twoQ, twoTri]; ring

/-- **The form factors.**  `2Q(a,b) = (a+b)(3a+b+1)`. -/
theorem twoQ_factored (a b : ℤ) : twoQ a b = (a + b) * (3 * a + b + 1) := by
  simp only [twoQ]; ring

/-- **Positivity.**  On the index set of (9) -- `a, b >= 0` not both zero -- the form is positive,
so every term of the false-theta sum decays.  Immediate from the factorisation. -/
theorem twoQ_pos (a b : ℤ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hne : 0 < a + b) : 0 < twoQ a b := by
  rw [twoQ_factored]
  have h2 : 0 < 3 * a + b + 1 := by linarith
  exact mul_pos hne h2

/-- The form vanishes only at the origin of the index set. -/
theorem twoQ_eq_zero_iff (a b : ℤ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    twoQ a b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    by_contra hcon
    have hpos : 0 < a + b := by omega
    have hp := twoQ_pos a b ha hb hpos
    linarith
  · rintro ⟨rfl, rfl⟩
    simp [twoQ]

/-! ### Why the omitted endpoints are pentagonal

Step (5) -> (6) of the write-up is one sentence: "Euler's pentagonal theorem supplies the two
omitted endpoints `j = r-1, r`."  `K` sums `j` from `0` to `r-2` while `H` sums `0` to `r`, so the
difference is those two terms -- but *why* Euler's theorem should be the thing that supplies them
is left to the reader.

It is because **the two omitted exponents are exactly the generalized pentagonal numbers**:

  `T_r + (r-1)r = r(3r-1)/2`,      `T_r + r*r = r(3r+1)/2`,

and those are precisely the exponents in Euler's `(q;q)_inf = SUM (-1)^r q^(r(3r-1)/2)`.  The
sentence is not an appeal to a convenient identity; the endpoints *are* the pentagonal series, term
for term.

Doubled to stay integral, both are `ring` identities.  They also land consistently in the `(a,b)`
parametrisation of the previous section -- `j = r-1` is `(a,b) = (r-1,1)` and `j = r` is `(r,0)` --
which cross-checks the reindexing against the pentagonal theorem rather than taking either on
trust. -/

/-- Twice the generalized pentagonal number `r(3r-1)/2`. -/
def twoPent (r : ℤ) : ℤ := r * (3 * r - 1)

/-- Twice the other generalized pentagonal number `r(3r+1)/2`. -/
def twoPentAlt (r : ℤ) : ℤ := r * (3 * r + 1)

/-- **The `j = r-1` endpoint is pentagonal.** -/
theorem endpoint_lower (r : ℤ) : twoTri r + 2 * (r - 1) * r = twoPent r := by
  simp only [twoTri, twoPent]; ring

/-- **The `j = r` endpoint is the other pentagonal number.** -/
theorem endpoint_upper (r : ℤ) : twoTri r + 2 * r * r = twoPentAlt r := by
  simp only [twoTri, twoPentAlt]; ring

/-- In the `(a,b)` parametrisation the lower endpoint sits at `(r-1, 1)`. -/
theorem twoQ_at_pent_lower (r : ℤ) : twoQ (r - 1) 1 = twoPent r := by
  rw [twoQ_factored]
  simp only [twoPent]; ring

/-- In the `(a,b)` parametrisation the upper endpoint sits at `(r, 0)`. -/
theorem twoQ_at_pent_upper (r : ℤ) : twoQ r 0 = twoPentAlt r := by
  rw [twoQ_factored]
  simp only [twoPentAlt]; ring

/-- The two pentagonal families are distinct away from `r = 0`, so the endpoints do not collide --
which is what lets them be removed independently in (5) -> (6). -/
theorem twoPent_ne_twoPentAlt (r : ℤ) (hr : r ≠ 0) : twoPent r ≠ twoPentAlt r := by
  simp only [twoPent, twoPentAlt]
  intro h
  apply hr
  nlinarith [h, sq_nonneg r]

/-! ### Computed evidence: the identity, the threshold, and tightness

The whole reduction rests on the source's quoted identity (2), `u(0,n) + u(1,n) = (p(n)+N(0,n))/2`,
which is used and never checked here -- if it were false, `rank_difference_of_split` would be
certifying an implication from an impossible hypothesis.  Enumerating partitions by Dyson rank and
strongly unimodal sequences by peak position gives, for `1 <= n <= 25`:

* **Identity (2) holds at every `n`.**  Zero failures.  `2(u0+u1) = p+N` exactly, from `n = 1`.
* **The threshold `n >= 8` is NECESSARY.**  Claim (1) FAILS at `n = 3, 5, 7`, where
  `E_n = p(n) - 4u(1,n) = -1`.  The source states `n >= 8` without saying why; the reason is that
  the three odd values below it are genuine counterexamples, not an artefact of the method.
* **The bound is TIGHT.**  `E_11 = 0`.  So `ExactRange` cannot be strengthened to a strict
  inequality, and any formalisation that tried to prove `0 < E n` on the finite range would be
  attempting something false.

Table (n, p, N(0,n), u(0,n), u(1,n), E_n):
`(3, 3, 1, 1, 1, -1)`, `(5, 7, 1, 2, 2, -1)`, `(7, 15, 3, 5, 4, -1)`, `(8, 22, 2, 7, 5, 2)`,
`(11, 56, 6, 17, 14, 0)`, `(25, 1958, 134, 563, 483, 26)`.

This is evidence about the STATEMENTS, obtained by independent enumeration while the kernel is
unavailable; it is not a proof of anything and does not substitute for CI.  But it does establish
that the hypotheses being carried are satisfiable and that the constants are the right ones, which
is the failure mode a spine cannot otherwise detect: an implication from a false premise typechecks
perfectly. -/

/-- The `n >= 8` hypothesis is not decorative: at `n = 3, 5, 7` one has `E_n = -1 < 0`.  Recorded
as an arithmetic fact about the witnessed values, so the threshold is documented in Lean and not
only in prose. -/
theorem threshold_necessary_witness :
    (3 : ℤ) - 4 * 1 = -1 ∧ (7 : ℤ) - 4 * 2 = -1 ∧ (15 : ℤ) - 4 * 4 = -1 := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-- Tightness at `n = 11`: `p(11) - 4*u(1,11) = 56 - 56 = 0`, so `ExactRange`'s `0 <= E n` cannot
be strengthened to `0 < E n`. -/
theorem tight_at_eleven : (56 : ℤ) - 4 * 14 = 0 := by norm_num

/-! ### The objects, written down — a correction to the round-121 audit

Round 121 fenced this row with *"three of its four objects cannot be WRITTEN"*, on the evidence that
`Dyson` and `stronglyUnimodal` occur nowhere in Mathlib.  **Round 122 showed that reasoning to be
unreliable** — `RieszBasis` was absent as a NAME while the notion built in three lines from what the
library had — so the same test is applied here, and **half the fence does not survive it.**

`p(n)` and `N(m,n)` are definable immediately.  Mathlib has `Nat.Partition` as a structure with a
`Multiset ℕ` of parts, `DecidableEq` derived and a `Fintype` instance, so the partition count is a
`Fintype.card` and **Dyson's rank — largest part minus number of parts — is one line.**

What does NOT follow is that the row is reachable.  `u(m,n)` counts strongly unimodal SEQUENCES; the
objects are definable (a strictly increasing run, a peak, a strictly decreasing run) but the
`Fintype` needed to count them is real work, and, decisively, **the two estimates are unaffected**:
identity (2) is an unproved bijective identity, `ExactRange` is a 10⁴-term big-integer check with
`native_decide` banned and Euler's pentagonal *theorem* absent, and `AnalyticRange` is effective
circle-method asymptotics on a library with no partition asymptotics at all.

So the correction is narrow and worth making anyway: **two of the four functions in the row's
statement are now REAL OBJECTS rather than abstract parameters**, and the spine below is stated
against them.
-/

/-- The largest part of a partition; `0` for the empty partition of `0`. -/
def maxPart {n : ℕ} (p : Nat.Partition n) : ℕ := p.parts.toFinset.sup id

/-- **DYSON'S RANK** of a partition: largest part minus number of parts. -/
def dysonRank {n : ℕ} (p : Nat.Partition n) : ℤ :=
  (maxPart p : ℤ) - (Multiset.card p.parts : ℤ)

/-- `p(n)`, the number of partitions of `n`. -/
def partitionCount (n : ℕ) : ℕ := Fintype.card (Nat.Partition n)

/-- `N(m, n)`, the number of partitions of `n` whose Dyson rank is `m`. -/
def rankCount (m : ℤ) (n : ℕ) : ℕ :=
  (Finset.univ.filter fun p : Nat.Partition n => dysonRank p = m).card

/-- **THE SPINE, WITH `p` AND `N` AT THE REAL OBJECTS.**

Identical to `rank_difference_of_split` except that the partition count and the rank count are no
longer abstract parameters.  What is still carried is exactly the analysis: identity (2) relating
the unimodal counts to `p` and `N`, and the two ranges. -/
theorem rank_difference_of_split_real {u0 u1 E : ℕ → ℤ}
    (hE : ∀ n : ℕ, E n = (partitionCount n : ℤ) - 4 * u1 n)
    (hid : ∀ n : ℕ, 2 * (u0 n + u1 n) = (partitionCount n : ℤ) + (rankCount 0 n : ℤ))
    (hex : ExactRange E) (han : AnalyticRange E) :
    ∀ n : ℕ, 8 ≤ n → (rankCount 0 n : ℤ) ≤ 2 * (u0 n - u1 n) :=
  rank_difference_of_split hE hid hex han

/-! ### Strongly unimodal sequences, and the row's statement in full

The last abstract function is `u(m,n)`.  Round 124 priced it as a `Fintype` construction; **that
pricing was wrong, and the reason is worth keeping**: it assumed the count had to be a
`Finset.card`.  `Nat.card` is defined for ANY type (and is `0` on an infinite one), so a counting
function needs no finiteness proof at all.  **Finiteness is needed to COMPUTE, and nothing here
computes.**

**The definition is the standard one, and the source does not restate it.**  `solution.md` says only
"strongly unimodal sequences of weight `n` and rank `m`" and cites Bringmann--Jennings-Shaffer--
Mahlburg--Rhoades for the fixed-rank generating function.  The standard object is a sequence of
positive integers

    a₁ < a₂ < ⋯ < a_r < c > b_s > ⋯ > b₁

of total weight `n`, with rank `s − r`: terms after the peak minus terms before it.  Encoded here as
a `List ℕ` together with the peak's index.

**Why counting PAIRS is counting sequences.**  `unimodalCount` counts pairs `(l, k)`.  The peak
index is determined by the list -- a strictly-increasing-then-strictly-decreasing list has a unique
argmax -- so no sequence is counted twice.  *This is stated, not proved; it is a property of the
encoding, not an input to any theorem below.*
-/

/-- `l` is a strongly unimodal sequence with its peak at index `k`: positive entries, strictly
increasing up to and including position `k`, strictly decreasing from `k` onwards. -/
def IsStronglyUnimodal (l : List ℕ) (k : ℕ) : Prop :=
  (∀ a ∈ l, 0 < a) ∧ k < l.length ∧
    List.Chain' (· < ·) (l.take (k + 1)) ∧ List.Chain' (· > ·) (l.drop k)

/-- The rank: terms after the peak minus terms before it.  Written over `ℤ` throughout, so no
truncated subtraction can occur. -/
def sequenceRank (l : List ℕ) (k : ℕ) : ℤ := (l.length : ℤ) - 1 - 2 * (k : ℤ)

/-- `u(m, n)`, the number of strongly unimodal sequences of weight `n` and rank `m`.

`Nat.card` rather than `Finset.card`: the statement needs a number, not an algorithm. -/
noncomputable def unimodalCount (m : ℤ) (n : ℕ) : ℕ :=
  Nat.card {q : List ℕ × ℕ //
    IsStronglyUnimodal q.1 q.2 ∧ sequenceRank q.1 q.2 = m ∧ q.1.sum = n}

/-- **MathDB #364074, STATED IN FULL.**

Every function is now a real object -- the partition count, the Dyson-rank count and the unimodal
counts -- and exactly three hypotheses are carried, all of them the analysis the source supplies:
identity (2), the finite range, and the major-arc range.

That is the whole point of writing it this way.  With `p, N, u₀, u₁` as abstract parameters the
hypothesis set was satisfiable by construction and an error in it could never surface; against the
real objects, a false premise is a real error. -/
theorem rank_difference_of_split_full {E : ℕ → ℤ}
    (hE : ∀ n : ℕ, E n = (partitionCount n : ℤ) - 4 * (unimodalCount 1 n : ℤ))
    (hid : ∀ n : ℕ, 2 * ((unimodalCount 0 n : ℤ) + (unimodalCount 1 n : ℤ))
      = (partitionCount n : ℤ) + (rankCount 0 n : ℤ))
    (hex : ExactRange E) (han : AnalyticRange E) :
    ∀ n : ℕ, 8 ≤ n →
      (rankCount 0 n : ℤ) ≤ 2 * ((unimodalCount 0 n : ℤ) - (unimodalCount 1 n : ℤ)) :=
  rank_difference_of_split hE hid hex han

/-! ### The carried hypotheses are NOT vacuous — the definitions are the intended objects

`rank_difference_of_split_full` carries identity (2), `ExactRange` and `AnalyticRange` against REAL
objects.  That is only worth anything if `partitionCount`, `rankCount` and `unimodalCount` denote
what the source means by `p(n)`, `N(0,n)` and `u(m,n)` -- a Lean definition that merely looks
plausible would let the whole spine certify an implication from a false premise.

**Checked, 2026-09-06.**  Python models of the Lean definitions -- `dysonRank` as largest part minus
number of parts over `Nat.Partition`, and `IsStronglyUnimodal` as a positive list strictly
increasing to index `k` and strictly decreasing from it -- reproduce **every row** of this
file's own
table:

    n  |  p(n) | N(0,n) | u(0,n) | u(1,n) |  E_n
     3 |     3 |      1 |      1 |      1 |   -1
     5 |     7 |      1 |      2 |      2 |   -1
     7 |    15 |      3 |      5 |      4 |   -1
     8 |    22 |      2 |      7 |      5 |    2
    11 |    56 |      6 |     17 |     14 |    0
    25 |  1958 |    134 |    563 |    483 |   26

Six rows, six exact matches -- **including `u(0,25) = 563` and `u(1,25) = 483`**, which no plausible
but wrong encoding of "strongly unimodal of rank `m`" would hit.  **Identity (2) itself holds for
every `n` from 1 to 25**, so the hypothesis the spine carries is satisfied wherever it can be
computed.

**And the pairs-vs-sequences caveat is discharged empirically.**  `unimodalCount` counts PAIRS
`(l, k)`; round 125 stated without proof that the peak index is unique, so pairs and sequences count
the same.  Over every positive-integer list of weight up to 12: **275 pairs, 275 distinct lists,
and no list with two valid peak indices.**  (A Lean proof is a short argument -- if `k < k'` both
worked, then `l k < l (k+1)` from the ascending run and `l k > l (k+1)` from the descending one --
and it is the next brick here.)

**The design cost of `Nat.card`, recorded.**  Round 125 used `Nat.card` so the counting function
needed no `Fintype`, which made the STATEMENT one line.  The price is that `unimodalCount` is
noncomputable, so **no `decide` can evaluate it** and identity (2) cannot be witnessed in the kernel
at a concrete `n` -- the arithmetic below is a witness about the VALUES, in the style this file
already uses for `threshold_necessary_witness` and `tight_at_eleven`, not about the definitions.
*"A count needs no `Fintype` unless something computes it"* is right; the corollary is that **the
moment you want a witness, you need the computable version.**
-/

/-- **IDENTITY (2) AT THE SIX TABULATED VALUES.**  `2(u₀+u₁) = p + N` at `n = 3, 5, 7, 8, 11, 25`,
with the counts as computed from the definitions in this file. -/
theorem identity_two_witnesses :
    2 * ((1 : ℤ) + 1) = 3 + 1 ∧
      2 * ((2 : ℤ) + 2) = 7 + 1 ∧
      2 * ((5 : ℤ) + 4) = 15 + 3 ∧
      2 * ((7 : ℤ) + 5) = 22 + 2 ∧
      2 * ((17 : ℤ) + 14) = 56 + 6 ∧
      2 * ((563 : ℤ) + 483) = 1958 + 134 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-! ### The peak index is unique — counting pairs IS counting sequences

`unimodalCount` counts PAIRS `(l, k)` of a sequence and its peak index.  Round 125 stated, without
proof, that this counts sequences: a strictly-up-then-strictly-down list has a unique argmax.  That
was the one faithfulness caveat left in this row's definitions, and it is discharged here.

The argument is two lines of mathematics.  If `k < k'` both served as peaks, then `k + 1 ≤ k'`, so
the pair `(l[k], l[k+1])` sits inside the ASCENDING run `l.take (k'+1)` and also at the front of the
DESCENDING run `l.drop k` — giving `l[k] < l[k+1]` and `l[k] > l[k+1]` at once.

**`Chain'` is a thin alias.**  Batteries defines `Chain' : (α → α → Prop) → List α → Prop :=
(IsChain · ·)`, so the usable API is `IsChain` — `isChain_iff_getElem`, not the `chain'_*` names one
would guess.  (Grepping `Mathlib/Data/List/Chain.lean` for `chain'_iff_get` returns nothing; the
lemma lives in `Batteries/Data/List/Lemmas.lean` under the other name.)

Measured before being written: over every positive-integer list of weight up to 12, **275 pairs and
275 distinct lists**, with no list admitting two valid peak indices. -/
theorem not_two_peaks {l : List ℕ} {k k' : ℕ} (hlt : k < k')
    (h : IsStronglyUnimodal l k) (h' : IsStronglyUnimodal l k') : False := by
  obtain ⟨-, -, -, hdn⟩ := h
  obtain ⟨-, hk', hup, -⟩ := h'
  have hk1 : k + 1 < l.length := lt_of_le_of_lt (Nat.succ_le_of_lt hlt) hk'
  have hdn' := List.isChain_iff_getElem.mp hdn 0
    (by first | (simp only [List.length_drop]; omega) | (simp; omega))
  have hup' := List.isChain_iff_getElem.mp hup k
    (by first | (simp only [List.length_take]; omega) | (simp; omega))
  first
    | simp only [List.getElem_drop, List.getElem_take, Nat.add_zero,
        Nat.zero_add] at hdn' hup'
    | simp [List.getElem_drop, List.getElem_take] at hdn' hup'
  omega

/-- **THE PEAK INDEX IS UNIQUE.**  So `unimodalCount`'s pairs `(l, k)` are in bijection with the
strongly unimodal sequences themselves, and the count is the source's `u(m, n)`. -/
theorem peak_unique {l : List ℕ} {k k' : ℕ}
    (h : IsStronglyUnimodal l k) (h' : IsStronglyUnimodal l k') : k = k' := by
  rcases lt_trichotomy k k' with hlt | heq | hgt
  · exact absurd (not_two_peaks hlt h h') not_false
  · exact heq
  · exact absurd (not_two_peaks hgt h' h) not_false

/-! ### The computable count, and why it needed Mathlib's `Composition`

Round 134 recorded the design cost of `Nat.card`: `unimodalCount` is noncomputable, so no `decide`
can evaluate it, and `identity_two_witnesses` is therefore a statement about NUMBERS -- `2*(1+1) =
3+1` and five more -- that says nothing whatever about the definitions in this file.  Its own
corollary was *"the moment you want a WITNESS, you need the computable version."*  Here it is.

**The enumeration was already in Mathlib, under a name this row never used.**  A strongly unimodal
sequence of weight `n` is a list of POSITIVE naturals summing to `n` -- and that is verbatim
`Composition n`, whose `blocks_pos` and `blocks_sum` fields are exactly the two side conditions.
It carries `Fintype`, via `compositionEquiv` to `Finset (Fin (n-1))`, of cardinality `2 ^ (n-1)`.
Grepping for the NOTION rather than for "unimodal" or for an invented name is what found it; a
hand-rolled enumeration would have owed its own completeness proof.

**The peak index is bounded by `n`, so the second component is a `Fin n`.**  `k < l.length`, and
every entry is at least `1`, so `l.length ≤ l.sum = n` -- which `Composition.length_le` already
proves.  Without that bound the product type is infinite and no `Fintype` exists.

**`Chain'` needed its instance written by hand.**  `Decidable (l.IsChain R)` exists in
Batteries, but
`Chain'` is a plain `def` -- not `abbrev`, not `@[reducible]` -- so instance resolution will not
unfold it.  `inferInstanceAs` crosses the gap, because the two are definitionally equal.

Measured before being written: over `Composition n × Fin n` this counts `u(0,n) = 1, 1, 1, 2, 5, 7,
17` and `u(1,n) = 0, 0, 1, 2, 4, 5, 14` at `n = 1, 2, 3, 5, 7, 8, 11` -- **every tabulated value in
this file's own table** -- with zero violations of either invariant over all `n ≤ 13`. -/
instance decidableStronglyUnimodal (l : List ℕ) (k : ℕ) :
    Decidable (IsStronglyUnimodal l k) :=
  inferInstanceAs (Decidable ((∀ a ∈ l, 0 < a) ∧ k < l.length ∧
    List.IsChain (· < ·) (l.take (k + 1)) ∧ List.IsChain (· > ·) (l.drop k)))

/-- `u(m, n)` again, as a `Finset.card` over a `Fintype`: the computable twin of `unimodalCount`. -/
def unimodalCountC (m : ℤ) (n : ℕ) : ℕ :=
  (Finset.univ.filter fun q : Composition n × Fin n =>
    IsStronglyUnimodal q.1.blocks q.2 ∧ sequenceRank q.1.blocks q.2 = m).card

/-- The peak index of a weight-`n` strongly unimodal sequence lies below `n`. -/
theorem peak_lt_of_stronglyUnimodal {l : List ℕ} {k n : ℕ}
    (h : IsStronglyUnimodal l k) (hs : l.sum = n) : k < n := by
  let c : Composition n := ⟨l, fun hi => h.1 _ hi, hs⟩
  have hle : c.blocks.length ≤ n := by
    have h2 := c.length_le
    rwa [← Composition.blocks_length] at h2
  exact lt_of_lt_of_le h.2.1 hle

/-- **THE TWO COUNTS AGREE.**  Without this the computable definition is merely a second definition
that could be wrong; with it, every kernel evaluation of `unimodalCountC` is a fact about
`unimodalCount`, and so about the objects the spine's hypotheses are stated over. -/
theorem unimodalCount_eq_countC (m : ℤ) (n : ℕ) :
    unimodalCount m n = unimodalCountC m n := by
  have e : {q : List ℕ × ℕ //
        IsStronglyUnimodal q.1 q.2 ∧ sequenceRank q.1 q.2 = m ∧ q.1.sum = n} ≃
      {q : Composition n × Fin n //
        IsStronglyUnimodal q.1.blocks q.2 ∧ sequenceRank q.1.blocks q.2 = m} :=
    { toFun := fun q =>
        ⟨(⟨q.1.1, fun hi => q.2.1.1 _ hi, q.2.2.2⟩,
          ⟨q.1.2, peak_lt_of_stronglyUnimodal q.2.1 q.2.2.2⟩), q.2.1, q.2.2.1⟩
      invFun := fun q => ⟨(q.1.1.blocks, q.1.2), q.2.1, q.2.2, q.1.1.blocks_sum⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [unimodalCount, Nat.card_congr e, Nat.card_eq_fintype_card, unimodalCountC,
    Fintype.card_subtype]

/-! ### The kernel witness, and the enumeration that had to be paid for

Round 136 proved `unimodalCount_eq_countC` -- the noncomputable count equals a `Finset.card` over
Mathlib's `Composition n` -- and then measured, in four probes, that no `decide` can pass
through it:
`Composition`'s elements are produced by `orderEmbOfFin` -> `orderIsoOfFin` -> `Finset.sort`, merge
sort over a quotient, which does not kernel-reduce.  `Finset.card` never inspects the elements
and so
reduces fine; `Finset.filter` must produce them and so does not.  **The wall is one Mathlib
function,
upstream of everything here.**

So the enumeration is written out, and the completeness lemma that reusing `Composition` skipped is
the price.  `compsAux` is **fuel-driven, hence structurally recursive on its first argument** -- a
well-founded definition would land on the very wall just measured, since `WellFounded.fix` does not
reduce either.  Fuel `n` is exactly enough for weight `n`: every part is at least `1`, so a
weight-`n`
list has at most `n` of them, and that bound is what `mem_compsAux` carries as its third conjunct.

Probed BEFORE anything was built on it, which is round 136's own rule: `compsOf 3` reduces to
`[[1,1,1], [1,2], [2,1], [3]]`, `(compsOf 8).length` to `128`, and the full weight-8 count to
`7` and
`5` -- all by `decide`, all in the kernel.

The `length ≤ sum` step is `List.length_le_sum_of_one_le`, which Mathlib already had -- found by
grepping the NOTION after a hand-rolled induction failed, because the first attempt had `clear`ed
away the very positivity hypothesis the bound needs.

`toFinset` rather than a list count, deliberately: it dedups, so no `Nodup` lemma for `compsOf` is
owed.  The pair set is `(compsOf n).toFinset ×ˢ Finset.range n`, the second factor bounded by
`peak_lt_of_stronglyUnimodal`, which round 136 already banked. -/
def compsAux : ℕ → ℕ → List (List ℕ)
  | _, 0 => [[]]
  | 0, _ + 1 => []
  | f + 1, m + 1 => (List.range (m + 1)).flatMap fun j =>
      (compsAux f (m - j)).map fun l => (j + 1) :: l

/-- Every list of positive naturals of weight `n`, with fuel `n` -- enough for `n` parts. -/
def compsOf (n : ℕ) : List (List ℕ) := compsAux n n

theorem compsAux_zero_right (f : ℕ) : compsAux f 0 = [[]] := by cases f <;> rfl

theorem compsAux_succ (f m : ℕ) : compsAux (f + 1) (m + 1) =
    (List.range (m + 1)).flatMap fun j =>
      (compsAux f (m - j)).map fun l => (j + 1) :: l := rfl

/-- **THE ENUMERATION IS SOUND AND COMPLETE.**  The fuel bound is carried as a third conjunct
because the induction needs it: without it the backward direction cannot place a list in the
sub-enumeration it came from. -/
theorem mem_compsAux : ∀ (f n : ℕ) (l : List ℕ),
    l ∈ compsAux f n ↔ (∀ a ∈ l, 0 < a) ∧ l.sum = n ∧ l.length ≤ f := by
  intro f
  induction f with
  | zero =>
      intro n l
      cases n with
      | zero =>
          rw [compsAux_zero_right, List.mem_singleton]
          constructor
          · rintro rfl; simp
          · rintro ⟨-, -, hlen⟩
            cases l with
            | nil => rfl
            | cons a t => simp only [List.length_cons] at hlen; omega
      | succ m =>
          simp only [compsAux, List.not_mem_nil, false_iff, not_and]
          intro _ hsum
          cases l with
          | nil => simp only [List.sum_nil] at hsum; omega
          | cons a t => intro hlen; simp only [List.length_cons] at hlen; omega
  | succ f ih =>
      intro n l
      cases n with
      | zero =>
          rw [compsAux_zero_right, List.mem_singleton]
          constructor
          · rintro rfl; simp
          · rintro ⟨hpos, hsum, -⟩
            cases l with
            | nil => rfl
            | cons a t =>
                have ha := hpos a (by simp)
                simp only [List.sum_cons] at hsum
                omega
      | succ m =>
          rw [compsAux_succ]
          simp only [List.mem_flatMap, List.mem_map, List.mem_range]
          constructor
          · rintro ⟨j, hj, l', hl', rfl⟩
            rw [ih] at hl'
            obtain ⟨hpos, hsum, hlen⟩ := hl'
            refine ⟨fun a ha => ?_, ?_, ?_⟩
            · rcases List.mem_cons.mp ha with rfl | ha
              · omega
              · exact hpos a ha
            · simp only [List.sum_cons]; omega
            · simp only [List.length_cons]; omega
          · rintro ⟨hpos, hsum, hlen⟩
            cases l with
            | nil => simp only [List.sum_nil] at hsum; omega
            | cons a t =>
                have ha := hpos a (by simp)
                obtain ⟨j, rfl⟩ : ∃ j, a = j + 1 := ⟨a - 1, by omega⟩
                simp only [List.sum_cons] at hsum
                simp only [List.length_cons] at hlen
                refine ⟨j, by omega, t, ?_, rfl⟩
                rw [ih]
                exact ⟨fun b hb => hpos b (List.mem_cons_of_mem _ hb), by omega, by omega⟩

/-- Weight `n` and positive parts force at most `n` parts, so fuel `n` loses nothing. -/
theorem mem_compsOf (n : ℕ) (l : List ℕ) :
    l ∈ compsOf n ↔ (∀ a ∈ l, 0 < a) ∧ l.sum = n := by
  rw [compsOf, mem_compsAux]
  refine ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, ?_⟩⟩
  obtain ⟨hpos, hsum⟩ := h
  subst hsum
  exact List.length_le_sum_of_one_le l fun a ha => hpos a ha

/-- The weight-`n` pairs, as a `Finset`.  `toFinset` dedups, so no `Nodup` lemma is owed. -/
def compPairs (n : ℕ) : Finset (List ℕ × ℕ) :=
  (compsOf n).toFinset ×ˢ Finset.range n

/-- `u(m, n)` a third time -- now over an enumeration the KERNEL can evaluate. -/
def unimodalCountK (m : ℤ) (n : ℕ) : ℕ :=
  ((compPairs n).filter fun q =>
    IsStronglyUnimodal q.1 q.2 ∧ sequenceRank q.1 q.2 = m).card

theorem mem_filter_compPairs (m : ℤ) (n : ℕ) (q : List ℕ × ℕ) :
    q ∈ (compPairs n).filter
        (fun q => IsStronglyUnimodal q.1 q.2 ∧ sequenceRank q.1 q.2 = m) ↔
      IsStronglyUnimodal q.1 q.2 ∧ sequenceRank q.1 q.2 = m ∧ q.1.sum = n := by
  rw [Finset.mem_filter, compPairs, Finset.mem_product, List.mem_toFinset,
    Finset.mem_range, mem_compsOf]
  constructor
  · rintro ⟨⟨⟨-, hsum⟩, -⟩, hsu, hrk⟩
    exact ⟨hsu, hrk, hsum⟩
  · rintro ⟨hsu, hrk, hsum⟩
    exact ⟨⟨⟨hsu.1, hsum⟩, peak_lt_of_stronglyUnimodal hsu hsum⟩, hsu, hrk⟩

/-- **THE KERNEL-EVALUABLE COUNT AGREES WITH THE DEFINITION.** -/
theorem unimodalCount_eq_countK (m : ℤ) (n : ℕ) :
    unimodalCount m n = unimodalCountK m n := by
  rw [unimodalCount, unimodalCountK, ← Fintype.card_coe, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr
    (Equiv.subtypeEquivRight fun q => (mem_filter_compPairs m n q).symm)

/-! ### Identity (2), at last as a statement about the definitions

`identity_two_witnesses` (round 134) is six arithmetic tautologies: `2*(1+1) = 3+1` and five more.
It records the tabulated NUMBERS and says nothing about `unimodalCount`.  The two theorems below say
it about the definition -- the counts are computed by the kernel from `IsStronglyUnimodal` and
`sequenceRank` themselves, and `unimodalCount_eq_countK` transports them back.

`n = 8` is the first index where identity (2) is not degenerate and is inside `2^(n-1) = 128`
compositions.  `n = 25` would be 16 million and is out of reach for `decide`; `native_decide` is
banned, so the tabulated `u(0,25) = 563` stays a measurement. -/
set_option maxRecDepth 100000 in
theorem unimodalCount_eight :
    unimodalCount 0 8 = 7 ∧ unimodalCount 1 8 = 5 := by
  refine ⟨?_, ?_⟩
  · rw [unimodalCount_eq_countK]; decide
  · rw [unimodalCount_eq_countK]; decide

/-- **IDENTITY (2) AT `n = 8`, ABOUT THE DEFINITIONS.**  `2(u₀ + u₁) = p + N` reads `2(7+5) = 22+2`;
the two `u` values are the ones this file's own `unimodalCount` denotes, computed in the kernel. -/
theorem identity_two_at_eight :
    2 * ((unimodalCount 0 8 : ℤ) + (unimodalCount 1 8 : ℤ)) = 22 + 2 := by
  rw [unimodalCount_eight.1, unimodalCount_eight.2]
  norm_num

/-! ### The partition side, so identity (2) at `n = 8` has no literals left in it

`identity_two_at_eight` read `2*(unimodalCount 0 8 + unimodalCount 1 8) = 22 + 2`.  After round 137
the left side was computed by the kernel from the definitions; the right side was still two literals
standing in for `partitionCount 8` and `rankCount 0 8`.  This closes that.

**`Nat.Partition`'s `Fintype` hits the same wall as `Composition`'s.**  Probed first, per the rule
round 136 paid for: `partitionCount 3 = 3` fails to `decide` -- at THREE partitions, so again not a
size problem.  The unfold trace names `Multiset.decidableEq`, `List.decidablePerm` and
`Nat.instDecidableEqPartition`: deciding equality of partitions means deciding a permutation between
representatives of a quotient, and the kernel cannot get there.

**So the enumeration is reused, not rebuilt.**  A partition of `n` is a composition of `n` whose
parts do not increase, so `partsOf n` is one `List.filter` away from round 137's `compsOf n`, and
`mem_compsOf` supplies positivity and weight for free.  Only the sortedness predicate is new, and it
is written **`Bool`-valued on purpose**: `filter` then needs no `Decidable` instance at all,
which is
the class of thing that has twice failed to reduce here.

**The correspondence is `Multiset.sort`, and it never needs to reduce.**  `partitionEquiv` maps a
partition to `p.parts.sort (· ≥ ·)` -- merge sort, the very function round 136 measured as
kernel-opaque.  That is harmless: the equiv is consumed only by `Fintype.card_congr`, which is
proof-level.  **What must reduce is the COUNT, and the count lives on the list side.**  Sortedness
pins the inverse: two sorted lists with the same multiset are equal (`List.Perm.eq_of_pairwise'`),
which is what makes the map a bijection rather than merely a surjection.

Measured before being written (`<scratchpad>/partsof.py`): `p(n) = 3, 7, 15, 22, 56` and
`N(0,n) = 1, 1, 3, 2, 6` at `n = 3, 5, 7, 8, 11` -- every tabulated value -- and the two rank-zero
partitions of `8` are `[3,3,2]` and `[4,2,1,1]`.  Probed in the kernel before being written:
`(partsOf 8).toFinset.card` reduces to `22` and the rank-zero filter to `2`. -/
def nonIncB : List ℕ → Bool
  | [] => true
  | [_] => true
  | a :: b :: t => decide (b ≤ a) && nonIncB (b :: t)

/-- The partitions of `n`, as non-increasing lists: the compositions that do not increase. -/
def partsOf (n : ℕ) : List (List ℕ) := (compsOf n).filter nonIncB

/-- `dysonRank` transcribed to a list: largest part minus number of parts.  Written with
`toFinset.sup` rather than a head or a `foldr max` so it matches `maxPart` on the nose. -/
def listRank (l : List ℕ) : ℤ := ((l.toFinset.sup id : ℕ) : ℤ) - (l.length : ℤ)

theorem nonIncB_iff_isChain : ∀ l : List ℕ, nonIncB l = true ↔ List.IsChain (· ≥ ·) l
  | [] => by simp [nonIncB]
  | [_] => by simp [nonIncB]
  | a :: b :: t => by
      rw [nonIncB, List.isChain_cons_cons, Bool.and_eq_true, decide_eq_true_iff,
        nonIncB_iff_isChain (b :: t)]

theorem nonIncB_iff (l : List ℕ) : nonIncB l = true ↔ List.Pairwise (· ≥ ·) l := by
  rw [nonIncB_iff_isChain, List.isChain_iff_pairwise]

/-- Positivity and weight come straight from round 137's `mem_compsOf`; only sortedness is new. -/
theorem mem_partsOf (n : ℕ) (l : List ℕ) :
    l ∈ partsOf n ↔ (∀ a ∈ l, 0 < a) ∧ l.sum = n ∧ List.Pairwise (· ≥ ·) l := by
  rw [partsOf, List.mem_filter, mem_compsOf, nonIncB_iff]
  tauto

/-- **PARTITIONS ARE THEIR SORTED PART LISTS.**  `sort` itself is kernel-opaque; it is used only
inside proofs, never inside the count. -/
noncomputable def partitionEquiv (n : ℕ) :
    Nat.Partition n ≃ {l : List ℕ // l ∈ partsOf n} where
  toFun p :=
    ⟨p.parts.sort (· ≥ ·), by
      rw [mem_partsOf]
      refine ⟨fun a ha => p.parts_pos ((Multiset.mem_sort _).mp ha), ?_,
        Multiset.pairwise_sort _ _⟩
      rw [← Multiset.sum_coe, Multiset.sort_eq, p.parts_sum]⟩
  invFun l :=
    ⟨(l.1 : Multiset ℕ), fun {i} hi => ((mem_partsOf n l.1).mp l.2).1 i hi, by
      rw [Multiset.sum_coe]; exact ((mem_partsOf n l.1).mp l.2).2.1⟩
  left_inv p := Nat.Partition.ext (Multiset.sort_eq _ _)
  right_inv l := by
    apply Subtype.ext
    show (l.1 : Multiset ℕ).sort (· ≥ ·) = l.1
    refine List.Perm.eq_of_pairwise' (Multiset.pairwise_sort _ _)
      ((mem_partsOf n l.1).mp l.2).2.2 ?_
    exact Multiset.coe_eq_coe.mp (Multiset.sort_eq (l.1 : Multiset ℕ) (· ≥ ·))

theorem dysonRank_eq_listRank (n : ℕ) (p : Nat.Partition n) :
    dysonRank p = listRank (p.parts.sort (· ≥ ·)) := by
  rw [dysonRank, listRank, maxPart, ← List.toFinset_coe, Multiset.sort_eq,
    Multiset.length_sort]

/-- The counts, over an enumeration the kernel can evaluate. -/
def partitionCountK (n : ℕ) : ℕ := (partsOf n).toFinset.card

def rankCountK (m : ℤ) (n : ℕ) : ℕ :=
  ((partsOf n).toFinset.filter fun l => listRank l = m).card

theorem partitionCount_eq_countK (n : ℕ) : partitionCount n = partitionCountK n := by
  rw [partitionCount, partitionCountK, ← Fintype.card_coe]
  exact (Fintype.card_congr (partitionEquiv n)).trans
    (Fintype.card_congr (Equiv.subtypeEquivRight fun _ => List.mem_toFinset.symm))

theorem rankCount_eq_countK (m : ℤ) (n : ℕ) : rankCount m n = rankCountK m n := by
  have h1 : rankCount m n = Fintype.card {p : Nat.Partition n // dysonRank p = m} := by
    rw [rankCount, Fintype.card_subtype]
  have h2 : rankCountK m n
      = Fintype.card ((partsOf n).toFinset.filter fun l => listRank l = m) := by
    rw [rankCountK, Fintype.card_coe]
  rw [h1, h2]
  refine Fintype.card_congr (((partitionEquiv n).subtypeEquiv fun p => ?_).trans
    ((Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ partsOf n)
        fun l => listRank l = m).trans (Equiv.subtypeEquivRight fun l => ?_)))
  · show dysonRank p = m ↔ listRank (p.parts.sort (· ≥ ·)) = m
    rw [dysonRank_eq_listRank]
  · rw [Finset.mem_filter, List.mem_toFinset]

/-! ### Identity (2) at `n = 8`, with nothing left standing in for a definition -/

set_option maxRecDepth 100000 in
theorem partitionCount_eight : partitionCount 8 = 22 ∧ rankCount 0 8 = 2 := by
  refine ⟨?_, ?_⟩
  · rw [partitionCount_eq_countK]; decide
  · rw [rankCount_eq_countK]; decide

/-- **IDENTITY (2) AT `n = 8`, ENTIRELY ABOUT THE DEFINITIONS.**  `2(u₀ + u₁) = p + N` with all four
counts computed by the kernel from `IsStronglyUnimodal`, `sequenceRank`, `Nat.Partition` and
`dysonRank` -- no tabulated number appears in the statement. -/
theorem identity_two_at_eight_full :
    2 * ((unimodalCount 0 8 : ℤ) + (unimodalCount 1 8 : ℤ))
      = (partitionCount 8 : ℤ) + (rankCount 0 8 : ℤ) := by
  rw [unimodalCount_eight.1, unimodalCount_eight.2, partitionCount_eight.1,
    partitionCount_eight.2]
  norm_num

/-! ### IDENTITY (2), KERNEL-VERIFIED AT `n = 9` AND `n = 10`

The range was `n ≤ 8`.  Identity (2) in general is research-level — a bijection the source does not
supply — so the honest thing the formalization can do is widen the range over which the kernel has
checked it against the definitions themselves.  Nothing here is tabulated: every one of the eight
numbers is computed by `decide` from `IsStronglyUnimodal`, `sequenceRank`, `Nat.Partition` and
`dysonRank`, through the same `countK` bridges the `n = 8` case uses.

    n = 9   2(10 + 7)  = 34 = 30 + 4
    n = 10  2(13 + 10) = 46 = 42 + 4

The cost grows with the composition count (`2^(n-1)` compositions times `Fin n`), which is why the
file records `n = 25` as out of reach for `decide` and `native_decide` as banned.  `n = 10` is
5× the `n = 8` work and still lands. -/
set_option maxRecDepth 200000 in
theorem unimodalCount_nine :
    unimodalCount 0 9 = 10 ∧ unimodalCount 1 9 = 7 := by
  refine ⟨?_, ?_⟩
  · rw [unimodalCount_eq_countK]; decide
  · rw [unimodalCount_eq_countK]; decide

set_option maxRecDepth 200000 in
theorem partitionCount_nine : partitionCount 9 = 30 ∧ rankCount 0 9 = 4 := by
  refine ⟨?_, ?_⟩
  · rw [partitionCount_eq_countK]; decide
  · rw [rankCount_eq_countK]; decide

/-- **IDENTITY (2) AT `n = 9`, ENTIRELY ABOUT THE DEFINITIONS.** -/
theorem identity_two_at_nine_full :
    2 * ((unimodalCount 0 9 : ℤ) + (unimodalCount 1 9 : ℤ))
      = (partitionCount 9 : ℤ) + (rankCount 0 9 : ℤ) := by
  rw [unimodalCount_nine.1, unimodalCount_nine.2, partitionCount_nine.1,
    partitionCount_nine.2]
  norm_num

set_option maxRecDepth 200000 in
set_option maxHeartbeats 2000000 in
theorem unimodalCount_ten :
    unimodalCount 0 10 = 13 ∧ unimodalCount 1 10 = 10 := by
  refine ⟨?_, ?_⟩
  · rw [unimodalCount_eq_countK]; decide
  · rw [unimodalCount_eq_countK]; decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 2000000 in
theorem partitionCount_ten : partitionCount 10 = 42 ∧ rankCount 0 10 = 4 := by
  refine ⟨?_, ?_⟩
  · rw [partitionCount_eq_countK]; decide
  · rw [rankCount_eq_countK]; decide

/-- **IDENTITY (2) AT `n = 10`, ENTIRELY ABOUT THE DEFINITIONS.** -/
theorem identity_two_at_ten_full :
    2 * ((unimodalCount 0 10 : ℤ) + (unimodalCount 1 10 : ℤ))
      = (partitionCount 10 : ℤ) + (rankCount 0 10 : ℤ) := by
  rw [unimodalCount_ten.1, unimodalCount_ten.2, partitionCount_ten.1,
    partitionCount_ten.2]
  norm_num

section Reindex

/-! ### The reindexing of (7) into (9), as a statement about SUMS

The header records that the exponent identity underneath the write-up's `(7) → (9)`
reparametrisation is exact, and that what was still owed is *"the bijectivity of the reindexing
as a statement about sums"*.  This section pays that, and in doing so spends the exponent and
endpoint lemmas, which until now were proved and **consumed by nothing**.

`toNine (r, j) = (j, r − j)` and `toSeven (a, b) = (a + b, a)` are mutually inverse on the two
index sets — `(7)`'s `r ≥ 1`, `0 ≤ j ≤ r` and `(9)`'s `a, b ≥ 0`, `a + b ≥ 1` — and the map
carries `(7)`'s exponent `T_r + j·r` to `(9)`'s form `Q(a, b)`, doubled to stay in `ℤ`.
`sum_reindex` is then the sum identity for an ARBITRARY summand `f`, on the truncation
`a + b ≤ N` that makes both index sets finite.  The truncation is not a weakening of the source's
claim: the write-up's sums are over `r ≤ N` for the same `N`, since `r = a + b`.

`endpoints_pentagonal` is the `(5) → (6)` endpoint step: the two ends of the `j`-range land at
`(r−1, 1)` and `(r, 0)`, whose exponents are the two generalized pentagonal families, and those
families are distinct away from `r = 0`, which is what lets the ends be removed independently.

**What is still absent is unchanged**: the Euler–Boole expansion, the certified remainders, the
saddle point and the Arb interval arithmetic, i.e. `ExactRange` and `AnalyticRange`.  This closes
the reindexing, not the analysis.
-/

/-- `(7)`'s index set: `r ≥ 1` and `0 ≤ j ≤ r`. -/
def IdxSeven (rj : ℤ × ℤ) : Prop := 1 ≤ rj.1 ∧ 0 ≤ rj.2 ∧ rj.2 ≤ rj.1

/-- `(9)`'s index set: `a, b ≥ 0` and `a + b ≥ 1`. -/
def IdxNine (ab : ℤ × ℤ) : Prop := 0 ≤ ab.1 ∧ 0 ≤ ab.2 ∧ 1 ≤ ab.1 + ab.2

/-- The reparametrisation `r = a + b`, `j = a`, read as a map out of `(7)`'s indices. -/
def toNine (rj : ℤ × ℤ) : ℤ × ℤ := (rj.2, rj.1 - rj.2)

/-- Its inverse. -/
def toSeven (ab : ℤ × ℤ) : ℤ × ℤ := (ab.1 + ab.2, ab.1)

theorem toNine_mem {rj : ℤ × ℤ} (h : IdxSeven rj) : IdxNine (toNine rj) := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨h2, by simp only [toNine]; omega, by simp only [toNine]; omega⟩

theorem toSeven_mem {ab : ℤ × ℤ} (h : IdxNine ab) : IdxSeven (toSeven ab) := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨h3, h1, by simp only [toSeven]; omega⟩

theorem toSeven_toNine (rj : ℤ × ℤ) : toSeven (toNine rj) = rj := by
  simp only [toSeven, toNine]
  ext <;> simp

theorem toNine_toSeven (ab : ℤ × ℤ) : toNine (toSeven ab) = ab := by
  simp only [toSeven, toNine]
  ext <;> simp

/-- **The exponent is transported.**  `(7)`'s `T_r + j·r`, doubled, is `(9)`'s `2Q(a, b)`. -/
theorem exp_transport (rj : ℤ × ℤ) :
    twoTri rj.1 + 2 * rj.2 * rj.1 = twoQ (toNine rj).1 (toNine rj).2 := by
  simp only [toNine]
  rw [twoQ_eq_twoTri_add]
  simp only [twoTri]
  ring

/-- `(7)`'s indices with `r ≤ N`. -/
def S7 (N : ℤ) : Finset (ℤ × ℤ) :=
  ((Finset.Icc (1 : ℤ) N) ×ˢ (Finset.Icc (0 : ℤ) N)).filter (fun p => p.2 ≤ p.1)

/-- `(9)`'s indices with `a + b ≤ N`. -/
def S9 (N : ℤ) : Finset (ℤ × ℤ) :=
  ((Finset.Icc (0 : ℤ) N) ×ˢ (Finset.Icc (0 : ℤ) N)).filter
    (fun p => 1 ≤ p.1 + p.2 ∧ p.1 + p.2 ≤ N)

theorem mem_S7 {N : ℤ} {p : ℤ × ℤ} : p ∈ S7 N ↔ (1 ≤ p.1 ∧ p.1 ≤ N ∧ 0 ≤ p.2 ∧ p.2 ≤ p.1) := by
  simp only [S7, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  omega

theorem mem_S9 {N : ℤ} {p : ℤ × ℤ} :
    p ∈ S9 N ↔ (0 ≤ p.1 ∧ 0 ≤ p.2 ∧ 1 ≤ p.1 + p.2 ∧ p.1 + p.2 ≤ N) := by
  simp only [S9, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  omega

/-- **The reindexing, as a statement about sums.**  For every summand `f` and every truncation
`N`, summing `f` of `(7)`'s exponent over `(7)`'s indices equals summing `f` of `(9)`'s form over
`(9)`'s indices. -/
theorem sum_reindex (f : ℤ → ℤ) (N : ℤ) :
    ∑ p ∈ S7 N, f (twoTri p.1 + 2 * p.2 * p.1) = ∑ p ∈ S9 N, f (twoQ p.1 p.2) := by
  refine Finset.sum_nbij' toNine toSeven ?_ ?_ ?_ ?_ ?_
  · intro p hp
    rw [mem_S7] at hp
    rw [mem_S9]
    simp only [toNine]
    omega
  · intro p hp
    rw [mem_S9] at hp
    rw [mem_S7]
    simp only [toSeven]
    omega
  · intro p _
    exact toSeven_toNine p
  · intro p _
    exact toNine_toSeven p
  · intro p _
    exact congrArg f (exp_transport p)

/-- **The `(5) → (6)` endpoint step.**  The two ends of the `j`-range are the two generalized
pentagonal families, they sit at `(r−1, 1)` and `(r, 0)` after the reindexing, and the families
are distinct away from `r = 0`. -/
theorem endpoints_pentagonal (r : ℤ) :
    toNine (r, r - 1) = (r - 1, 1) ∧ toNine (r, r) = (r, 0)
      ∧ twoTri r + 2 * (r - 1) * r = twoPent r
      ∧ twoTri r + 2 * r * r = twoPentAlt r
      ∧ twoQ (r - 1) 1 = twoPent r ∧ twoQ r 0 = twoPentAlt r
      ∧ (r ≠ 0 → twoPent r ≠ twoPentAlt r) := by
  refine ⟨?_, ?_, endpoint_lower r, endpoint_upper r, twoQ_at_pent_lower r,
    twoQ_at_pent_upper r, twoPent_ne_twoPentAlt r⟩
  · simp only [toNine]
    ext <;> simp
  · simp only [toNine]
    ext <;> simp

/-- **Positivity on `(9)`'s index set**, which is what makes the reindexed exponents nonzero. -/
theorem twoQ_pos_on_IdxNine {ab : ℤ × ℤ} (h : IdxNine ab) : 0 < twoQ ab.1 ab.2 := by
  obtain ⟨h1, h2, h3⟩ := h
  exact twoQ_pos ab.1 ab.2 h1 h2 (by omega)

end Reindex

end Principia.MathDB.P364074
