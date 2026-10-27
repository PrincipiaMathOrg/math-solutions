import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.LinearCombination
import Mathlib.RingTheory.Coprime.Basic

set_option autoImplicit false

/-!
# MathDB #335304 — Holt's Conjecture 17: four-digit permutiples are symmetric

Write-up: `mathdb-open-problems/problems/335304/solution.tex`, collaborator branch
`mathdb-results` of `antoshashakov/Principia-Math-In-Progress` (enrolled here 2026-09-30).
Source: Holt, arXiv:1702.04760v1, **Conjecture 17**.

If `[a;b,c,d] = k·[e;f,g,h]` with `(e,f,g,h)` a permutation of `(a,b,c,d)`, `d, h ≥ 2` and `k ≥ 2`
an integer, then `ad = eh` and `bc = fg` — every canonical four-digit continued-fraction
permutiple is symmetric in Holt's sense.

## The algebraic core, which is what this module proves

With `P = abcd + ab + ad + cd + 1` and `Q = bcd + b + d`, the continued fraction is `P/Q` in
lowest terms, and the whole argument runs on three algebraic facts:

* `det_identity` — `P·q₂ − Q·p₂ = 1` for the truncation `p₂/q₂ = [a;b,c]`. One `ring`.
* `two_L0_sub_U0` — the write-up's **explicit expansion**
  `2L₀ − U₀ = (x−1)(xyzw/x + 2(y+z+w)) + (y−1)(z−1)(w−1) + y+z+w+2`,
  which is what makes the ratio lemma a positivity statement rather than an estimate. One `ring`,
  and then `U0_lt_two_L0` is positivity term by term.
* the **twelve tabulated differences** `P − P'`, one for each positional permutation with
  `e ≠ a` and `h ≠ a`. Each is one `ring`, and together with the six `e = a` and six `h = a`
  cases they exhaust all 24 permutations.

## Why the ratio lemma is the engine

`PQ' = kP'Q` with `gcd(P',Q') = 1` gives `P' ∣ P`; the ratio lemma says the two continuants of a
common multiset differ by a factor below two; so `P = P'` and `Q' = kQ`. Everything after that is
divisibility bookkeeping on the twelve tabulated differences.

## Stage 2: the bracketing and Lemma `last`

Both are now proved, and the bracketing turned out **not** to be twenty-four `nlinarith` goals.
`Pc a b c d = a*b*c*d + (a*b + a*d + c*d) + 1` with the product symmetric, so each bound is a
**term-by-term** comparison of three edge products along the path `b-a-d-c`, and `Pc_reverse`
halves the twenty-four arrangements to twelve. The matchings were searched for by the verifier and
the twelve theorems are generated from that same search, so the hint lists cannot drift from the
checked ones. `lemma_last` is the divisibility core and `eq_of_ratio` is the write-up's `(equal)`.

## What is NOT proved here

Two things, and both are named.

* **The permutation plumbing.** `lt_two_mul_of_bracket` consumes two bracket instances; producing
  them for an arbitrary positional permutation of `(a,b,c,d)` needs the four digits sorted and the
  arrangement matched to one of the twelve theorems. That is a `List.Perm` decomposition with
  twenty-four leaves plus a sort -- combinatorial plumbing rather than mathematics, and it is the
  only thing between this module and the ratio lemma in the shape its consumer wants.
* **The case analysis A-E**, which disposes of the twelve tabulated rows. Stage 3.

## A finding: Lemma `last` is the only branch of the proof that ever fires

The verifier searched digits `1..15` and found 249 genuine permutiples -- **every one with
`h >= k`**, in fact with `h - k >= 2`. That is structural rather than an artefact of the range:
Cases A, C and E end in a *contradiction*, so their positional permutations cannot occur at all,
while Cases B and D end by *proving* `h >= k`. The case analysis is a funnel and `lemma_last` is
what it funnels into. The control that first asserted the opposite -- that `h < k` occurs and is
what Cases A-E handle -- failed, and this is what replaced it.

## Two hypotheses that are NOT what makes the statement true

Recorded because the verifier's first draft asserted the opposite and was refuted:

* `k ≥ 2` excludes a **trivial** case. At `k = 1` the two canonical expansions are equal, and
  canonical continued fractions are unique, so the permutation is the identity and the conclusion
  holds vacuously.
* `d, h ≥ 2` are **canonicity** conditions — `[a;b,c,1] = [a;b,c+1]` is not a four-digit canonical
  expansion at all — so they say which tuples are admissible, not why the implication holds.

The hypothesis that **is** load-bearing is that `(e,f,g,h)` is a permutation of `(a,b,c,d)`:
dropping it, `[4;1,2,2] = 3·[1;1,1,3]` with `4·2 ≠ 1·3`.
-/

namespace Principia.MathDB.P335304

/-! ## Continuants -/

/-- The numerator of `[a;b,c,d]`. -/
def Pc (a b c d : ℤ) : ℤ := a * b * c * d + a * b + a * d + c * d + 1

/-- The denominator of `[a;b,c,d]`. -/
def Qc (_a b c d : ℤ) : ℤ := b * c * d + b + d

/-- The numerator of the truncation `[a;b,c]`. -/
def Pc2 (a b c : ℤ) : ℤ := a * b * c + a + c

/-- The denominator of the truncation `[a;b,c]`. -/
def Qc2 (b c : ℤ) : ℤ := b * c + 1

/-- **The determinant identity.** This is what turns `P = P'` into information about `q₂`. -/
theorem det_identity (a b c d : ℤ) :
    Pc a b c d * Qc2 b c - Qc a b c d * Pc2 a b c = 1 := by
  simp only [Pc, Qc, Pc2, Qc2]
  ring

/-! ## The ratio lemma -/

/-- The write-up's lower bound for a continuant of the sorted multiset `x ≤ y ≤ z ≤ w`. -/
def L0 (x y z w : ℤ) : ℤ := x * y * z * w + x * (y + z + w) + 1

/-- The write-up's upper bound. -/
def U0 (x y z w : ℤ) : ℤ := x * y * z * w + w * (y + z) + y * z + 1

/-- **The explicit expansion.** Every summand is nonnegative when `1 ≤ x ≤ y ≤ z ≤ w`, which is
what makes the factor-of-two bound a positivity statement rather than an estimate. -/
theorem two_L0_sub_U0 (x y z w : ℤ) :
    2 * L0 x y z w - U0 x y z w
      = (x - 1) * (y * z * w + 2 * (y + z + w)) + (y - 1) * (z - 1) * (w - 1)
        + y + z + w + 2 := by
  simp only [L0, U0]
  ring

theorem U0_lt_two_L0 (x y z w : ℤ) (hx : 1 ≤ x) (hxy : x ≤ y) (hyz : y ≤ z) (hzw : z ≤ w) :
    U0 x y z w < 2 * L0 x y z w := by
  have hkey := two_L0_sub_U0 x y z w
  have hy1 : (1 : ℤ) ≤ y := le_trans hx hxy
  have hz1 : (1 : ℤ) ≤ z := le_trans hy1 hyz
  have hw1 : (1 : ℤ) ≤ w := le_trans hz1 hzw
  -- `positivity` and `nlinarith` cannot use the ordering hypotheses here, so the two
  -- nonnegativity facts are built by hand from `mul_nonneg`.
  have hyzw : 0 ≤ y * z * w :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  have h1 : 0 ≤ (x - 1) * (y * z * w + 2 * (y + z + w)) :=
    mul_nonneg (by linarith) (by linarith)
  have h2 : 0 ≤ (y - 1) * (z - 1) * (w - 1) :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  linarith

/-! ## The twelve tabulated differences

One for each positional permutation with `e ≠ a` and `h ≠ a`; the other twelve permutations are
the six with `e = a` (excluded because `a > e`) and the six with `h = a` (handled by the final
lemma, since `a ≥ k`). Together they exhaust all 24. -/

theorem diff_bacd (a b c d : ℤ) : Pc a b c d - Pc b a c d = d * (a - b) := by
  simp only [Pc]; ring

theorem diff_badc (a b c d : ℤ) : Pc a b c d - Pc b a d c = a * d - b * c := by
  simp only [Pc]; ring

theorem diff_bcad (a b c d : ℤ) :
    Pc a b c d - Pc b c a d = b * (a - c) - d * (b - c) := by
  simp only [Pc]; ring

theorem diff_bdac (a b c d : ℤ) :
    Pc a b c d - Pc b d a c = a * (b - c + d) - (b * c + b * d - c * d) := by
  simp only [Pc]; ring

theorem diff_cabd (a b c d : ℤ) :
    Pc a b c d - Pc c a b d = a * (b - c + d) - b * d := by
  simp only [Pc]; ring

theorem diff_cadb (a b c d : ℤ) :
    Pc a b c d - Pc c a d b = a * (b - c + d) - (b * c + b * d - c * d) := by
  simp only [Pc]; ring

theorem diff_cbad (a b c d : ℤ) : Pc a b c d - Pc c b a d = b * (a - c) := by
  simp only [Pc]; ring

theorem diff_cdab (a b c d : ℤ) : Pc a b c d - Pc c d a b = a * d - b * c := by
  simp only [Pc]; ring

theorem diff_dabc (a b c d : ℤ) : Pc a b c d - Pc d a b c = b * (a - c) := by
  simp only [Pc]; ring

theorem diff_dacb (a b c d : ℤ) :
    Pc a b c d - Pc d a c b = b * (a - c) - d * (b - c) := by
  simp only [Pc]; ring

theorem diff_dbac (a b c d : ℤ) :
    Pc a b c d - Pc d b a c = a * (b - c + d) - b * d := by
  simp only [Pc]; ring

theorem diff_dcab (a b c d : ℤ) : Pc a b c d - Pc d c a b = d * (a - b) := by
  simp only [Pc]; ring

/-! ## Case C, the one case the tabulated difference settles on its own -/

/-- **Case C's identity.** `cL − b = (c−1)(L−1) + d − 1` with `L = b−c+d`. It is an identity, not
an inequality -- stated with no hypotheses because it needs none; the write-up uses it together
with `c, d ≥ 1` and `L ≥ 1` to conclude `cL ≥ b`, and that step is stage 2. -/
theorem caseC_identity (b c d : ℤ) :
    c * (b - c + d) - b = (c - 1) * ((b - c + d) - 1) + d - 1 := by
  ring

/-- The consequence the write-up actually uses: `cL ≥ b`. -/
theorem caseC_le (b c d : ℤ) (hc : 1 ≤ c) (hd : 1 ≤ d) (hL : 1 ≤ b - c + d) :
    b ≤ c * (b - c + d) := by
  have h := caseC_identity b c d
  nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ c - 1) (by linarith : (0:ℤ) ≤ (b - c + d) - 1)]

/-! ## Stage 2, part one: the bracketing, term by term

`Pc a b c d = a*b*c*d + (a*b + a*d + c*d) + 1`, and the product is symmetric, so the whole
bracketing is a statement about the three edge products along the path `b-a-d-c`. Both bounds hold
**term by term**: each of the three target products is dominated by (or dominates) one of the
path's three products under `1 ≤ x ≤ y ≤ z ≤ w`. The matchings below were searched for by
`verify_335304.py` and the hint lists are generated from that same search, so they cannot drift
from the checked ones.
-/

/-- The one monotonicity fact every matching step uses. -/
theorem mul_le_mul_of_le {p q r s : ℤ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hpr : p ≤ r) (hqs : q ≤ s) :
    p * q ≤ r * s :=
  mul_le_mul hpr hqs hq (hp.trans hpr)

/-- Reversing an arrangement leaves its continuant unchanged: the path `b-a-d-c` reversed is the
path of `(d, c, b, a)`. This is what halves twenty-four bracketing cases to twelve. -/
theorem Pc_reverse (a b c d : ℤ) : Pc a b c d = Pc d c b a := by
  simp only [Pc]; ring

/-- **The ratio lemma, in the form its consumer uses.** Two continuants of arrangements of the
same sorted multiset are both bracketed by `L0` and `U0`, and `U0 < 2*L0`; so one is less than
twice the other, whichever way round they are taken. -/
theorem lt_two_mul_of_bracket {x y z w p q : ℤ} (hx : 1 ≤ x) (hxy : x ≤ y) (hyz : y ≤ z)
    (hzw : z ≤ w) (hq : q ≤ U0 x y z w) (hp : L0 x y z w ≤ p) : q < 2 * p := by
  have h := U0_lt_two_L0 x y z w hx hxy hyz hzw
  linarith

/-- Bracketing for the arrangement `(x, y, z, w)`; with `Pc_reverse` this and its reverse
`(w, z, y, x)` are two of the twenty-four. -/
theorem bracket_xyzw (x y z w : ℤ) (hx : 1 ≤ x) (hxy : x ≤ y) (hyz : y ≤ z)
    (hzw : z ≤ w) :
    L0 x y z w ≤ Pc x y z w ∧ Pc x y z w ≤ U0 x y z w := by
  have hn0 : (0 : ℤ) ≤ x := by linarith
  have hn1 : (0 : ℤ) ≤ y := by linarith
  have hn2 : (0 : ℤ) ≤ z := by linarith
  have hn3 : (0 : ℤ) ≤ w := by linarith
  have h01 : x ≤ y := hxy
  have h12 : y ≤ z := hyz
  have h23 : z ≤ w := hzw
  have h02 : x ≤ z := by linarith
  have h03 : x ≤ w := by linarith
  have h13 : y ≤ w := by linarith
  refine ⟨?_, ?_⟩
  · simp only [L0, Pc]
    -- xy <= xy, xz <= xw, xw <= zw
    linarith [mul_le_mul_of_le hn0 hn1 le_rfl le_rfl,
              mul_le_mul_of_le hn0 hn2 le_rfl h23,
              mul_le_mul_of_le hn0 hn3 h02 le_rfl]
  · simp only [U0, Pc]
    -- xw <= yw, zw <= zw, xy <= yz
    linarith [mul_le_mul_of_le hn0 hn3 h01 le_rfl,
              mul_le_mul_of_le hn2 hn3 le_rfl le_rfl,
              mul_le_mul_of_le hn0 hn1 h01 h12]

/-- Bracketing for the arrangement `(x, y, w, z)`; with `Pc_reverse` this and its reverse
`(z, w, y, x)` are two of the twenty-four. -/
theorem bracket_xywz (x y z w : ℤ) (hx : 1 ≤ x) (hxy : x ≤ y) (hyz : y ≤ z)
    (hzw : z ≤ w) :
    L0 x y z w ≤ Pc x y w z ∧ Pc x y w z ≤ U0 x y z w := by
  have hn0 : (0 : ℤ) ≤ x := by linarith
  have hn1 : (0 : ℤ) ≤ y := by linarith
  have hn2 : (0 : ℤ) ≤ z := by linarith
  have hn3 : (0 : ℤ) ≤ w := by linarith
  have h01 : x ≤ y := hxy
  have h12 : y ≤ z := hyz
  have h23 : z ≤ w := hzw
  have h02 : x ≤ z := by linarith
  have h03 : x ≤ w := by linarith
  have h13 : y ≤ w := by linarith
  refine ⟨?_, ?_⟩
  · simp only [L0, Pc]
    -- xy <= xy, xz <= xz, xw <= zw
    linarith [mul_le_mul_of_le hn0 hn1 le_rfl le_rfl,
              mul_le_mul_of_le hn0 hn2 le_rfl le_rfl,
              mul_le_mul_of_le hn0 hn3 h02 le_rfl]
  · simp only [U0, Pc]
    -- xy <= yw, zw <= zw, xz <= yz
    linarith [mul_le_mul_of_le hn0 hn1 h01 h13,
              mul_le_mul_of_le hn2 hn3 le_rfl le_rfl,
              mul_le_mul_of_le hn0 hn2 h01 le_rfl]

/-- Bracketing for the arrangement `(x, z, y, w)`; with `Pc_reverse` this and its reverse
`(w, y, z, x)` are two of the twenty-four. -/
theorem bracket_xzyw (x y z w : ℤ) (hx : 1 ≤ x) (hxy : x ≤ y) (hyz : y ≤ z)
    (hzw : z ≤ w) :
    L0 x y z w ≤ Pc x z y w ∧ Pc x z y w ≤ U0 x y z w := by
  have hn0 : (0 : ℤ) ≤ x := by linarith
  have hn1 : (0 : ℤ) ≤ y := by linarith
  have hn2 : (0 : ℤ) ≤ z := by linarith
  have hn3 : (0 : ℤ) ≤ w := by linarith
  have h01 : x ≤ y := hxy
  have h12 : y ≤ z := hyz
  have h23 : z ≤ w := hzw
  have h02 : x ≤ z := by linarith
  have h03 : x ≤ w := by linarith
  have h13 : y ≤ w := by linarith
  refine ⟨?_, ?_⟩
  · simp only [L0, Pc]
    -- xy <= xz, xz <= xw, xw <= yw
    linarith [mul_le_mul_of_le hn0 hn1 le_rfl h12,
              mul_le_mul_of_le hn0 hn2 le_rfl h23,
              mul_le_mul_of_le hn0 hn3 h01 le_rfl]
  · simp only [U0, Pc]
    -- xw <= yw, yw <= zw, xz <= yz
    linarith [mul_le_mul_of_le hn0 hn3 h01 le_rfl,
              mul_le_mul_of_le hn1 hn3 h12 le_rfl,
              mul_le_mul_of_le hn0 hn2 h01 le_rfl]

/-- Bracketing for the arrangement `(x, z, w, y)`; with `Pc_reverse` this and its reverse
`(y, w, z, x)` are two of the twenty-four. -/
theorem bracket_xzwy (x y z w : ℤ) (hx : 1 ≤ x) (hxy : x ≤ y) (hyz : y ≤ z)
    (hzw : z ≤ w) :
    L0 x y z w ≤ Pc x z w y ∧ Pc x z w y ≤ U0 x y z w := by
  have hn0 : (0 : ℤ) ≤ x := by linarith
  have hn1 : (0 : ℤ) ≤ y := by linarith
  have hn2 : (0 : ℤ) ≤ z := by linarith
  have hn3 : (0 : ℤ) ≤ w := by linarith
  have h01 : x ≤ y := hxy
  have h12 : y ≤ z := hyz
  have h23 : z ≤ w := hzw
  have h02 : x ≤ z := by linarith
  have h03 : x ≤ w := by linarith
  have h13 : y ≤ w := by linarith
  refine ⟨?_, ?_⟩
  · simp only [L0, Pc]
    -- xy <= xy, xz <= xz, xw <= yw
    linarith [mul_le_mul_of_le hn0 hn1 le_rfl le_rfl,
              mul_le_mul_of_le hn0 hn2 le_rfl le_rfl,
              mul_le_mul_of_le hn0 hn3 h01 le_rfl]
  · simp only [U0, Pc]
    -- xz <= yw, yw <= zw, xy <= yz
    linarith [mul_le_mul_of_le hn0 hn2 h01 h23,
              mul_le_mul_of_le hn1 hn3 h12 le_rfl,
              mul_le_mul_of_le hn0 hn1 h01 h12]

/-- Bracketing for the arrangement `(x, w, y, z)`; with `Pc_reverse` this and its reverse
`(z, y, w, x)` are two of the twenty-four. -/
theorem bracket_xwyz (x y z w : ℤ) (hx : 1 ≤ x) (hxy : x ≤ y) (hyz : y ≤ z)
    (hzw : z ≤ w) :
    L0 x y z w ≤ Pc x w y z ∧ Pc x w y z ≤ U0 x y z w := by
  have hn0 : (0 : ℤ) ≤ x := by linarith
  have hn1 : (0 : ℤ) ≤ y := by linarith
  have hn2 : (0 : ℤ) ≤ z := by linarith
  have hn3 : (0 : ℤ) ≤ w := by linarith
  have h01 : x ≤ y := hxy
  have h12 : y ≤ z := hyz
  have h23 : z ≤ w := hzw
  have h02 : x ≤ z := by linarith
  have h03 : x ≤ w := by linarith
  have h13 : y ≤ w := by linarith
  refine ⟨?_, ?_⟩
  · simp only [L0, Pc]
    -- xy <= xz, xz <= yz, xw <= xw
    linarith [mul_le_mul_of_le hn0 hn1 le_rfl h12,
              mul_le_mul_of_le hn0 hn2 h01 le_rfl,
              mul_le_mul_of_le hn0 hn3 le_rfl le_rfl]
  · simp only [U0, Pc]
    -- xw <= yw, xz <= zw, yz <= yz
    linarith [mul_le_mul_of_le hn0 hn3 h01 le_rfl,
              mul_le_mul_of_le hn0 hn2 h02 h23,
              mul_le_mul_of_le hn1 hn2 le_rfl le_rfl]

/-- Bracketing for the arrangement `(x, w, z, y)`; with `Pc_reverse` this and its reverse
`(y, z, w, x)` are two of the twenty-four. -/
theorem bracket_xwzy (x y z w : ℤ) (hx : 1 ≤ x) (hxy : x ≤ y) (hyz : y ≤ z)
    (hzw : z ≤ w) :
    L0 x y z w ≤ Pc x w z y ∧ Pc x w z y ≤ U0 x y z w := by
  have hn0 : (0 : ℤ) ≤ x := by linarith
  have hn1 : (0 : ℤ) ≤ y := by linarith
  have hn2 : (0 : ℤ) ≤ z := by linarith
  have hn3 : (0 : ℤ) ≤ w := by linarith
  have h01 : x ≤ y := hxy
  have h12 : y ≤ z := hyz
  have h23 : z ≤ w := hzw
  have h02 : x ≤ z := by linarith
  have h03 : x ≤ w := by linarith
  have h13 : y ≤ w := by linarith
  refine ⟨?_, ?_⟩
  · simp only [L0, Pc]
    -- xy <= xy, xz <= yz, xw <= xw
    linarith [mul_le_mul_of_le hn0 hn1 le_rfl le_rfl,
              mul_le_mul_of_le hn0 hn2 h01 le_rfl,
              mul_le_mul_of_le hn0 hn3 le_rfl le_rfl]
  · simp only [U0, Pc]
    -- xw <= yw, xy <= zw, yz <= yz
    linarith [mul_le_mul_of_le hn0 hn3 h01 le_rfl,
              mul_le_mul_of_le hn0 hn1 h02 h13,
              mul_le_mul_of_le hn1 hn2 le_rfl le_rfl]

/-- Bracketing for the arrangement `(y, x, z, w)`; with `Pc_reverse` this and its reverse
`(w, z, x, y)` are two of the twenty-four. -/
theorem bracket_yxzw (x y z w : ℤ) (hx : 1 ≤ x) (hxy : x ≤ y) (hyz : y ≤ z)
    (hzw : z ≤ w) :
    L0 x y z w ≤ Pc y x z w ∧ Pc y x z w ≤ U0 x y z w := by
  have hn0 : (0 : ℤ) ≤ x := by linarith
  have hn1 : (0 : ℤ) ≤ y := by linarith
  have hn2 : (0 : ℤ) ≤ z := by linarith
  have hn3 : (0 : ℤ) ≤ w := by linarith
  have h01 : x ≤ y := hxy
  have h12 : y ≤ z := hyz
  have h23 : z ≤ w := hzw
  have h02 : x ≤ z := by linarith
  have h03 : x ≤ w := by linarith
  have h13 : y ≤ w := by linarith
  refine ⟨?_, ?_⟩
  · simp only [L0, Pc]
    -- xy <= xy, xz <= yw, xw <= zw
    linarith [mul_le_mul_of_le hn0 hn1 le_rfl le_rfl,
              mul_le_mul_of_le hn0 hn2 h01 h23,
              mul_le_mul_of_le hn0 hn3 h02 le_rfl]
  · simp only [U0, Pc]
    -- yw <= yw, zw <= zw, xy <= yz
    linarith [mul_le_mul_of_le hn1 hn3 le_rfl le_rfl,
              mul_le_mul_of_le hn2 hn3 le_rfl le_rfl,
              mul_le_mul_of_le hn0 hn1 h01 h12]

/-- Bracketing for the arrangement `(y, x, w, z)`; with `Pc_reverse` this and its reverse
`(z, w, x, y)` are two of the twenty-four. -/
theorem bracket_yxwz (x y z w : ℤ) (hx : 1 ≤ x) (hxy : x ≤ y) (hyz : y ≤ z)
    (hzw : z ≤ w) :
    L0 x y z w ≤ Pc y x w z ∧ Pc y x w z ≤ U0 x y z w := by
  have hn0 : (0 : ℤ) ≤ x := by linarith
  have hn1 : (0 : ℤ) ≤ y := by linarith
  have hn2 : (0 : ℤ) ≤ z := by linarith
  have hn3 : (0 : ℤ) ≤ w := by linarith
  have h01 : x ≤ y := hxy
  have h12 : y ≤ z := hyz
  have h23 : z ≤ w := hzw
  have h02 : x ≤ z := by linarith
  have h03 : x ≤ w := by linarith
  have h13 : y ≤ w := by linarith
  refine ⟨?_, ?_⟩
  · simp only [L0, Pc]
    -- xy <= xy, xz <= yz, xw <= zw
    linarith [mul_le_mul_of_le hn0 hn1 le_rfl le_rfl,
              mul_le_mul_of_le hn0 hn2 h01 le_rfl,
              mul_le_mul_of_le hn0 hn3 h02 le_rfl]
  · simp only [U0, Pc]
    -- xy <= yw, zw <= zw, yz <= yz
    linarith [mul_le_mul_of_le hn0 hn1 h01 h13,
              mul_le_mul_of_le hn2 hn3 le_rfl le_rfl,
              mul_le_mul_of_le hn1 hn2 le_rfl le_rfl]

/-- Bracketing for the arrangement `(y, z, x, w)`; with `Pc_reverse` this and its reverse
`(w, x, z, y)` are two of the twenty-four. -/
theorem bracket_yzxw (x y z w : ℤ) (hx : 1 ≤ x) (hxy : x ≤ y) (hyz : y ≤ z)
    (hzw : z ≤ w) :
    L0 x y z w ≤ Pc y z x w ∧ Pc y z x w ≤ U0 x y z w := by
  have hn0 : (0 : ℤ) ≤ x := by linarith
  have hn1 : (0 : ℤ) ≤ y := by linarith
  have hn2 : (0 : ℤ) ≤ z := by linarith
  have hn3 : (0 : ℤ) ≤ w := by linarith
  have h01 : x ≤ y := hxy
  have h12 : y ≤ z := hyz
  have h23 : z ≤ w := hzw
  have h02 : x ≤ z := by linarith
  have h03 : x ≤ w := by linarith
  have h13 : y ≤ w := by linarith
  refine ⟨?_, ?_⟩
  · simp only [L0, Pc]
    -- xy <= yz, xz <= yw, xw <= xw
    linarith [mul_le_mul_of_le hn0 hn1 h01 h12,
              mul_le_mul_of_le hn0 hn2 h01 h23,
              mul_le_mul_of_le hn0 hn3 le_rfl le_rfl]
  · simp only [U0, Pc]
    -- yw <= yw, xw <= zw, yz <= yz
    linarith [mul_le_mul_of_le hn1 hn3 le_rfl le_rfl,
              mul_le_mul_of_le hn0 hn3 h02 le_rfl,
              mul_le_mul_of_le hn1 hn2 le_rfl le_rfl]

/-- Bracketing for the arrangement `(y, w, x, z)`; with `Pc_reverse` this and its reverse
`(z, x, w, y)` are two of the twenty-four. -/
theorem bracket_ywxz (x y z w : ℤ) (hx : 1 ≤ x) (hxy : x ≤ y) (hyz : y ≤ z)
    (hzw : z ≤ w) :
    L0 x y z w ≤ Pc y w x z ∧ Pc y w x z ≤ U0 x y z w := by
  have hn0 : (0 : ℤ) ≤ x := by linarith
  have hn1 : (0 : ℤ) ≤ y := by linarith
  have hn2 : (0 : ℤ) ≤ z := by linarith
  have hn3 : (0 : ℤ) ≤ w := by linarith
  have h01 : x ≤ y := hxy
  have h12 : y ≤ z := hyz
  have h23 : z ≤ w := hzw
  have h02 : x ≤ z := by linarith
  have h03 : x ≤ w := by linarith
  have h13 : y ≤ w := by linarith
  refine ⟨?_, ?_⟩
  · simp only [L0, Pc]
    -- xy <= yz, xz <= xz, xw <= yw
    linarith [mul_le_mul_of_le hn0 hn1 h01 h12,
              mul_le_mul_of_le hn0 hn2 le_rfl le_rfl,
              mul_le_mul_of_le hn0 hn3 h01 le_rfl]
  · simp only [U0, Pc]
    -- yw <= yw, yz <= zw, xz <= yz
    linarith [mul_le_mul_of_le hn1 hn3 le_rfl le_rfl,
              mul_le_mul_of_le hn1 hn2 h12 h23,
              mul_le_mul_of_le hn0 hn2 h01 le_rfl]

/-- Bracketing for the arrangement `(z, x, y, w)`; with `Pc_reverse` this and its reverse
`(w, y, x, z)` are two of the twenty-four. -/
theorem bracket_zxyw (x y z w : ℤ) (hx : 1 ≤ x) (hxy : x ≤ y) (hyz : y ≤ z)
    (hzw : z ≤ w) :
    L0 x y z w ≤ Pc z x y w ∧ Pc z x y w ≤ U0 x y z w := by
  have hn0 : (0 : ℤ) ≤ x := by linarith
  have hn1 : (0 : ℤ) ≤ y := by linarith
  have hn2 : (0 : ℤ) ≤ z := by linarith
  have hn3 : (0 : ℤ) ≤ w := by linarith
  have h01 : x ≤ y := hxy
  have h12 : y ≤ z := hyz
  have h23 : z ≤ w := hzw
  have h02 : x ≤ z := by linarith
  have h03 : x ≤ w := by linarith
  have h13 : y ≤ w := by linarith
  refine ⟨?_, ?_⟩
  · simp only [L0, Pc]
    -- xy <= xz, xz <= zw, xw <= yw
    linarith [mul_le_mul_of_le hn0 hn1 le_rfl h12,
              mul_le_mul_of_le hn0 hn2 h02 h23,
              mul_le_mul_of_le hn0 hn3 h01 le_rfl]
  · simp only [U0, Pc]
    -- yw <= yw, zw <= zw, xz <= yz
    linarith [mul_le_mul_of_le hn1 hn3 le_rfl le_rfl,
              mul_le_mul_of_le hn2 hn3 le_rfl le_rfl,
              mul_le_mul_of_le hn0 hn2 h01 le_rfl]

/-- Bracketing for the arrangement `(z, y, x, w)`; with `Pc_reverse` this and its reverse
`(w, x, y, z)` are two of the twenty-four. -/
theorem bracket_zyxw (x y z w : ℤ) (hx : 1 ≤ x) (hxy : x ≤ y) (hyz : y ≤ z)
    (hzw : z ≤ w) :
    L0 x y z w ≤ Pc z y x w ∧ Pc z y x w ≤ U0 x y z w := by
  have hn0 : (0 : ℤ) ≤ x := by linarith
  have hn1 : (0 : ℤ) ≤ y := by linarith
  have hn2 : (0 : ℤ) ≤ z := by linarith
  have hn3 : (0 : ℤ) ≤ w := by linarith
  have h01 : x ≤ y := hxy
  have h12 : y ≤ z := hyz
  have h23 : z ≤ w := hzw
  have h02 : x ≤ z := by linarith
  have h03 : x ≤ w := by linarith
  have h13 : y ≤ w := by linarith
  refine ⟨?_, ?_⟩
  · simp only [L0, Pc]
    -- xy <= yz, xz <= zw, xw <= xw
    linarith [mul_le_mul_of_le hn0 hn1 h01 h12,
              mul_le_mul_of_le hn0 hn2 h02 h23,
              mul_le_mul_of_le hn0 hn3 le_rfl le_rfl]
  · simp only [U0, Pc]
    -- xw <= yw, zw <= zw, yz <= yz
    linarith [mul_le_mul_of_le hn0 hn3 h01 le_rfl,
              mul_le_mul_of_le hn2 hn3 le_rfl le_rfl,
              mul_le_mul_of_le hn1 hn2 le_rfl le_rfl]

/-! ## Stage 2, part two: Lemma `last`, which is the only branch of the proof that ever fires

The verifier searched digits `1..15` for genuine permutiples and found **249**, every one of them
with `h ≥ k` — indeed with `h - k ≥ 2`. That is not an accident of the range: Cases A, C and E of
the write-up end in a *contradiction*, so their positional permutations cannot occur at all, and
Cases B and D end by *proving* `h ≥ k`. So the case analysis is a funnel, and this lemma is the
thing it funnels into.
-/

/-- `P' = h·p₂' + e·f + 1`, which is why `P' > h·p₂'`. -/
theorem Pc_eq_mul_Pc2 (e f g h : ℤ) : Pc e f g h = h * Pc2 e f g + e * f + 1 := by
  simp only [Pc, Pc2]; ring

/-- `P - p₂` in manifestly positive form: every summand is nonnegative for `a, b, c, d ≥ 1`. -/
theorem Pc_sub_Pc2 (a b c d : ℤ) :
    Pc a b c d - Pc2 a b c
      = a * b * c * (d - 1) + a * (b - 1) + c * (d - 1) + a * d + 1 := by
  simp only [Pc, Pc2]; ring

theorem Pc2_pos (a b c : ℤ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) : 0 < Pc2 a b c := by
  have h : 0 ≤ a * b * c :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  simp only [Pc2]; linarith

theorem Pc2_lt_Pc (a b c d : ℤ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hd : 1 ≤ d) :
    Pc2 a b c < Pc a b c d := by
  have hkey := Pc_sub_Pc2 a b c d
  have h1 : 0 ≤ a * b * c * (d - 1) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)) (by linarith)
  have h2 : 0 ≤ a * (b - 1) := mul_nonneg (by linarith) (by linarith)
  have h3 : 0 ≤ c * (d - 1) := mul_nonneg (by linarith) (by linarith)
  have h4 : 0 ≤ a * d := mul_nonneg (by linarith) (by linarith)
  linarith

theorem Pc_pos (a b c d : ℤ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hd : 1 ≤ d) :
    0 < Pc a b c d := by
  have h := Pc2_lt_Pc a b c d ha hb hc hd
  have h' := Pc2_pos a b c ha hb hc
  linarith

theorem Qc_pos (a b c d : ℤ) (hb : 1 ≤ b) (hc : 1 ≤ c) (hd : 1 ≤ d) : 0 < Qc a b c d := by
  have h : 0 ≤ b * c * d :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  simp only [Qc]; linarith

/-- Coprimality of numerator and denominator, straight off the determinant identity — this is the
one place the identity proved in stage 1 becomes load-bearing rather than decorative. -/
theorem isCoprime_Pc_Qc (a b c d : ℤ) : IsCoprime (Pc a b c d) (Qc a b c d) :=
  ⟨Qc2 b c, -Pc2 a b c, by linear_combination det_identity a b c d⟩

/-- If `q ∣ p`, both are positive and `p < 2q`, then `p = q`. The ratio lemma's only consumer. -/
theorem eq_of_dvd_of_lt_two_mul {p q : ℤ} (hq : 0 < q) (hp : 0 < p) (hdvd : q ∣ p)
    (hlt : p < 2 * q) : p = q := by
  obtain ⟨t, ht⟩ := hdvd
  have ht1 : t = 1 := by
    rcases lt_trichotomy t 1 with hl | he | hg
    · exfalso
      have h0 : t ≤ 0 := by omega
      have : q * t ≤ q * 0 := mul_le_mul_of_nonneg_left h0 hq.le
      simp only [mul_zero] at this
      omega
    · exact he
    · exfalso
      have h2 : 2 ≤ t := by omega
      have : q * 2 ≤ q * t := mul_le_mul_of_nonneg_left h2 hq.le
      omega
  rw [ht, ht1, mul_one]

/-- The write-up's `(equal)`: from `P·Q' = k·P'·Q` and the ratio bound, `P = P'` and `Q' = kQ`. -/
theorem eq_of_ratio (a b c d e f g h k : ℤ)
    (hPpos : 0 < Pc a b c d) (hP'pos : 0 < Pc e f g h)
    (heq : Pc a b c d * Qc e f g h = k * Pc e f g h * Qc a b c d)
    (hratio : Pc a b c d < 2 * Pc e f g h) :
    Pc a b c d = Pc e f g h ∧ Qc e f g h = k * Qc a b c d := by
  have hcop : IsCoprime (Pc e f g h) (Qc e f g h) := isCoprime_Pc_Qc e f g h
  have hdvd : Pc e f g h ∣ Pc a b c d * Qc e f g h :=
    ⟨k * Qc a b c d, by linear_combination heq⟩
  have hdvd' : Pc e f g h ∣ Pc a b c d := hcop.dvd_of_dvd_mul_right hdvd
  have hPP : Pc a b c d = Pc e f g h := eq_of_dvd_of_lt_two_mul hP'pos hPpos hdvd' hratio
  refine ⟨hPP, ?_⟩
  have : Pc a b c d * Qc e f g h = Pc a b c d * (k * Qc a b c d) := by
    rw [heq, hPP]; ring
  exact mul_left_cancel₀ hPpos.ne' this

/-- **Lemma `last`.** If `h ≥ k` then `ad = eh` and `bc = fg`.

The chain: `0 < p₂ < P` and `0 < k·p₂' ≤ h·p₂' < P' = P`, so the difference `p₂ - k·p₂'` lies
strictly between `-P` and `P`; the two determinant identities make `P` divide it; so it is zero,
and then `P·(q₂ - q₂') = 0` forces `q₂ = q₂'`, which is `bc = fg`. The product equality finishes
`ad = eh`. -/
theorem lemma_last (a b c d e f g h k : ℤ)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hd : 1 ≤ d)
    (he : 1 ≤ e) (hf : 1 ≤ f) (hg : 1 ≤ g) (hk : 1 ≤ k)
    (hhk : k ≤ h)
    (hprod : a * b * c * d = e * f * g * h)
    (hPP : Pc a b c d = Pc e f g h)
    (hQQ : Qc e f g h = k * Qc a b c d) :
    a * d = e * h ∧ b * c = f * g := by
  have hP : 0 < Pc a b c d := Pc_pos a b c d ha hb hc hd
  have hdet := det_identity a b c d
  -- the second determinant identity, rewritten through `P' = P` and `Q' = kQ`
  have hdet2 : Pc a b c d * Qc2 f g - k * Qc a b c d * Pc2 e f g = 1 := by
    rw [hPP, ← hQQ]; exact det_identity e f g h
  -- subtracting them: `P·(q₂ - q₂') = Q·(p₂ - k·p₂')`
  have key : Pc a b c d * (Qc2 b c - Qc2 f g)
      = Qc a b c d * (Pc2 a b c - k * Pc2 e f g) := by
    linear_combination hdet - hdet2
  have hdvd : Pc a b c d ∣ Qc a b c d * (Pc2 a b c - k * Pc2 e f g) :=
    ⟨Qc2 b c - Qc2 f g, key.symm⟩
  have hdvd' : Pc a b c d ∣ Pc2 a b c - k * Pc2 e f g :=
    (isCoprime_Pc_Qc a b c d).dvd_of_dvd_mul_left hdvd
  -- the two bounds that trap the difference strictly inside `(-P, P)`
  have hp2 : 0 < Pc2 a b c := Pc2_pos a b c ha hb hc
  have hp2lt : Pc2 a b c < Pc a b c d := Pc2_lt_Pc a b c d ha hb hc hd
  have hp2' : 0 < Pc2 e f g := Pc2_pos e f g he hf hg
  have hkp2' : 0 < k * Pc2 e f g := mul_pos (by linarith) hp2'
  have hkp2lt : k * Pc2 e f g < Pc a b c d := by
    have hmono : k * Pc2 e f g ≤ h * Pc2 e f g :=
      mul_le_mul_of_nonneg_right hhk hp2'.le
    have hsplit : Pc e f g h = h * Pc2 e f g + e * f + 1 := Pc_eq_mul_Pc2 e f g h
    have hef : 1 ≤ e * f := by nlinarith
    rw [hPP]; linarith
  -- so it is zero
  have hzero : Pc2 a b c - k * Pc2 e f g = 0 := by
    obtain ⟨t, ht⟩ := hdvd'
    have ht0 : t = 0 := by
      rcases lt_trichotomy t 0 with hl | he0 | hgt
      · exfalso
        have h1 : t ≤ -1 := by omega
        have : Pc a b c d * t ≤ Pc a b c d * (-1) := mul_le_mul_of_nonneg_left h1 hP.le
        rw [← ht] at this; linarith
      · exact he0
      · exfalso
        have h1 : 1 ≤ t := by omega
        have : Pc a b c d * 1 ≤ Pc a b c d * t := mul_le_mul_of_nonneg_left h1 hP.le
        rw [← ht] at this; linarith
    rw [ht, ht0, mul_zero]
  -- and then `q₂ = q₂'`
  have hq : Qc2 b c = Qc2 f g := by
    rw [hzero, mul_zero] at key
    rcases mul_eq_zero.mp key with h' | h'
    · exact absurd h' hP.ne'
    · linarith
  have hbc : b * c = f * g := by simp only [Qc2] at hq; linarith
  refine ⟨?_, hbc⟩
  have hbcpos : 0 < b * c := mul_pos (by linarith) (by linarith)
  -- rewriting `hbc` in the goal hits BOTH sides and leaves `a*d*(f*g) = e*h*(f*g)`, which no
  -- longer matches the product equality; so rewrite only the right-hand side.
  have hrhs : e * h * (b * c) = e * f * g * h := by rw [hbc]; ring
  have hmul : a * d * (b * c) = e * h * (b * c) := by
    rw [hrhs]; linear_combination hprod
  exact mul_right_cancel₀ hbcpos.ne' hmul

/-! ## The other twelve arrangements: the bracketing now covers all twenty-four

The named residue says the permutation plumbing is *"a `List.Perm` decomposition with twenty-four
leaves plus a sort"*.  **Twelve of those leaves are now supplied.**  The twelve `bracket_*`
theorems above are one representative per reversal pair — `xyzw` and `wzyx`, `xywz` and `zwyx`,
and so on — so `Pc_reverse` hands over the other twelve for the price of one lemma each.

`bracket_reverse` is that lemma: the bracket is invariant under reversing an arrangement, because
the continuant is.  The twelve companions below then **consume all twelve** of the original
bracket theorems, which were orphans until now, and together the twenty-four arrangements of a
sorted `1 ≤ x ≤ y ≤ z ≤ w` are covered exhaustively.

**What remains of that residue is the SORT**, not the case split: given four digits in arbitrary
order, produce `x ≤ y ≤ z ≤ w` and the matching arrangement name.  The twenty-four-leaf part is
done. -/

/-- **The bracket is invariant under reversing an arrangement**, because `Pc` is. -/
theorem bracket_reverse {x y z w p q r s : ℤ}
    (h : L0 x y z w ≤ Pc p q r s ∧ Pc p q r s ≤ U0 x y z w) :
    L0 x y z w ≤ Pc s r q p ∧ Pc s r q p ≤ U0 x y z w := by
  rw [← Pc_reverse p q r s]
  exact h

variable (x y z w : ℤ)

theorem bracket_wzyx (hx : 1 ≤ x) (hxy : x ≤ y) (hyz : y ≤ z) (hzw : z ≤ w) :
    L0 x y z w ≤ Pc w z y x ∧ Pc w z y x ≤ U0 x y z w :=
  bracket_reverse (bracket_xyzw x y z w hx hxy hyz hzw)

theorem bracket_zwyx (hx : 1 ≤ x) (hxy : x ≤ y) (hyz : y ≤ z) (hzw : z ≤ w) :
    L0 x y z w ≤ Pc z w y x ∧ Pc z w y x ≤ U0 x y z w :=
  bracket_reverse (bracket_xywz x y z w hx hxy hyz hzw)

theorem bracket_wyzx (hx : 1 ≤ x) (hxy : x ≤ y) (hyz : y ≤ z) (hzw : z ≤ w) :
    L0 x y z w ≤ Pc w y z x ∧ Pc w y z x ≤ U0 x y z w :=
  bracket_reverse (bracket_xzyw x y z w hx hxy hyz hzw)

theorem bracket_ywzx (hx : 1 ≤ x) (hxy : x ≤ y) (hyz : y ≤ z) (hzw : z ≤ w) :
    L0 x y z w ≤ Pc y w z x ∧ Pc y w z x ≤ U0 x y z w :=
  bracket_reverse (bracket_xzwy x y z w hx hxy hyz hzw)

theorem bracket_zywx (hx : 1 ≤ x) (hxy : x ≤ y) (hyz : y ≤ z) (hzw : z ≤ w) :
    L0 x y z w ≤ Pc z y w x ∧ Pc z y w x ≤ U0 x y z w :=
  bracket_reverse (bracket_xwyz x y z w hx hxy hyz hzw)

theorem bracket_yzwx (hx : 1 ≤ x) (hxy : x ≤ y) (hyz : y ≤ z) (hzw : z ≤ w) :
    L0 x y z w ≤ Pc y z w x ∧ Pc y z w x ≤ U0 x y z w :=
  bracket_reverse (bracket_xwzy x y z w hx hxy hyz hzw)

theorem bracket_wzxy (hx : 1 ≤ x) (hxy : x ≤ y) (hyz : y ≤ z) (hzw : z ≤ w) :
    L0 x y z w ≤ Pc w z x y ∧ Pc w z x y ≤ U0 x y z w :=
  bracket_reverse (bracket_yxzw x y z w hx hxy hyz hzw)

theorem bracket_zwxy (hx : 1 ≤ x) (hxy : x ≤ y) (hyz : y ≤ z) (hzw : z ≤ w) :
    L0 x y z w ≤ Pc z w x y ∧ Pc z w x y ≤ U0 x y z w :=
  bracket_reverse (bracket_yxwz x y z w hx hxy hyz hzw)

theorem bracket_wxzy (hx : 1 ≤ x) (hxy : x ≤ y) (hyz : y ≤ z) (hzw : z ≤ w) :
    L0 x y z w ≤ Pc w x z y ∧ Pc w x z y ≤ U0 x y z w :=
  bracket_reverse (bracket_yzxw x y z w hx hxy hyz hzw)

theorem bracket_zxwy (hx : 1 ≤ x) (hxy : x ≤ y) (hyz : y ≤ z) (hzw : z ≤ w) :
    L0 x y z w ≤ Pc z x w y ∧ Pc z x w y ≤ U0 x y z w :=
  bracket_reverse (bracket_ywxz x y z w hx hxy hyz hzw)

theorem bracket_wyxz (hx : 1 ≤ x) (hxy : x ≤ y) (hyz : y ≤ z) (hzw : z ≤ w) :
    L0 x y z w ≤ Pc w y x z ∧ Pc w y x z ≤ U0 x y z w :=
  bracket_reverse (bracket_zxyw x y z w hx hxy hyz hzw)

theorem bracket_wxyz (hx : 1 ≤ x) (hxy : x ≤ y) (hyz : y ≤ z) (hzw : z ≤ w) :
    L0 x y z w ≤ Pc w x y z ∧ Pc w x y z ≤ U0 x y z w :=
  bracket_reverse (bracket_zyxw x y z w hx hxy hyz hzw)

/-! ## The twelve tabulated differences are SIX, and the other six are path-reversals

The write-up tabulates twelve differences, one per positional permutation with `e ≠ a` and
`h ≠ a`, and the module above transcribes all twelve.  **Six of them are redundant.**
`Pc_reverse` — already proved, and already used to halve the bracketing from twenty-four
arrangements to twelve — halves this table too, because the twelve permutations fall into six
reversal pairs, and a reversal pair has the *same continuant*, hence the *same difference*.

This is the same symmetry doing the same job one section later, and the write-up does not
remark on it: reading the table, the six coincidences among the right-hand sides
(`d(a−b)` twice, `b(a−c)` twice, `ad−bc` twice, and so on) look like arithmetic accidents.
They are not.  **So the case analysis A–E has six cases to dispose of, not twelve.**

`diff_pairs` records the collapse in the form that *consumes all twelve* tabulated lemmas, so
none of them is an orphan; `Pc_pairs_eq` gives the sharper underlying fact, that the paired
permutations have literally equal continuants, each a direct instance of `Pc_reverse`. -/

/-- **The paired permutations have EQUAL continuants** — six instances of `Pc_reverse`, which is
why the twelve tabulated differences take only six distinct values. -/
theorem Pc_pairs_eq (a b c d : ℤ) :
    Pc b a c d = Pc d c a b ∧ Pc c b a d = Pc d a b c ∧ Pc b a d c = Pc c d a b ∧
      Pc c a b d = Pc d b a c ∧ Pc b d a c = Pc c a d b ∧ Pc b c a d = Pc d a c b :=
  ⟨Pc_reverse b a c d, Pc_reverse c b a d, Pc_reverse b a d c,
   Pc_reverse c a b d, Pc_reverse b d a c, Pc_reverse b c a d⟩

/-- **The twelve tabulated differences collapse to six.**  Stated so that every one of the twelve
`diff_*` lemmas is consumed; before this, all twelve were orphans. -/
theorem diff_pairs (a b c d : ℤ) :
    Pc a b c d - Pc b a c d = Pc a b c d - Pc d c a b ∧
      Pc a b c d - Pc c b a d = Pc a b c d - Pc d a b c ∧
      Pc a b c d - Pc b a d c = Pc a b c d - Pc c d a b ∧
      Pc a b c d - Pc c a b d = Pc a b c d - Pc d b a c ∧
      Pc a b c d - Pc b d a c = Pc a b c d - Pc c a d b ∧
      Pc a b c d - Pc b c a d = Pc a b c d - Pc d a c b := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [diff_bacd, diff_dcab]
  · rw [diff_cbad, diff_dabc]
  · rw [diff_badc, diff_cdab]
  · rw [diff_cabd, diff_dbac]
  · rw [diff_bdac, diff_cadb]
  · rw [diff_bcad, diff_dacb]

/-! ### What a vanishing difference forces

`P = P′` means the tabulated difference is zero, and for the two pairs whose difference is a
single product that immediately pins two of the digits equal.  **This is the engine of the cases
that end in a contradiction**: under a strict ordering of the digits, `a = b` or `a = c` is
impossible, so those positional permutations cannot occur at all. -/

/-- If the `b a c d` arrangement has the same continuant and `d ≠ 0`, then `a = b`. -/
theorem eq_of_Pc_bacd (a b c d : ℤ) (hd : d ≠ 0) (h : Pc a b c d = Pc b a c d) : a = b := by
  have hz : d * (a - b) = 0 := by rw [← diff_bacd a b c d, h, sub_self]
  rcases mul_eq_zero.mp hz with h0 | h0
  · exact absurd h0 hd
  · linarith [sub_eq_zero.mp h0]

/-- If the `c b a d` arrangement has the same continuant and `b ≠ 0`, then `a = c`. -/
theorem eq_of_Pc_cbad (a b c d : ℤ) (hb : b ≠ 0) (h : Pc a b c d = Pc c b a d) : a = c := by
  have hz : b * (a - c) = 0 := by rw [← diff_cbad a b c d, h, sub_self]
  rcases mul_eq_zero.mp hz with h0 | h0
  · exact absurd h0 hb
  · linarith [sub_eq_zero.mp h0]

/-- **Two positional permutations are impossible outright under a strict ordering.**  With
`a < b` and `a < c` and positive digits, neither the `b a c d` nor the `c b a d` arrangement can
share the continuant — which is exactly how the contradicting cases close. -/
theorem Pc_bacd_ne (a b c d : ℤ) (hd : d ≠ 0) (hab : a < b) : Pc a b c d ≠ Pc b a c d :=
  fun h => absurd (eq_of_Pc_bacd a b c d hd h) (by linarith)

theorem Pc_cbad_ne (a b c d : ℤ) (hb : b ≠ 0) (hac : a < c) : Pc a b c d ≠ Pc c b a d :=
  fun h => absurd (eq_of_Pc_cbad a b c d hb h) (by linarith)

end Principia.MathDB.P335304
