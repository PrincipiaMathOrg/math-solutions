import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases

set_option autoImplicit false

/-!
# MathDB #370788 (and the equivalent #370787) — Chamberland–Dilcher Conjectures 7.4 and 7.3

Write-up: `mathdb-open-problems/problems/370788/solution.tex`, collaborator branch
`mathdb-results` of `antoshashakov/Principia-Math-In-Progress` (enrolled here 2026-09-30).
Source: M. Chamberland and K. Dilcher, *Sums of the floor function related to class numbers of
imaginary quadratic fields*, arXiv:2510.04387v1 (2025), **Conjectures 7.3–7.4**, pp. 21–22.

With `f(n) = Σ_{j=1}^{⌊n/4⌋} ⌊√(jn)⌋ − (n²−1)/12`, `δ(d) = 1` iff `d ≡ 3 (mod 4)`, and `H(d)`
the source's `h*(−d)·δ(d)` (so `H(3) = 1/3`), the two conjectures are, for odd squarefree `n`:

* **(7.3)**  `f(n) = (1−n)/4 · δ(n) − ½ Σ_{d∣n} H(d)`    (MathDB #370787)
* **(7.4)**  `H(n) = Σ_{d∣n} μ(n/d) ((1−d)/2 · δ(d) − 2 f(d))`    (MathDB #370788)

## What this module proves, and why it is the right thing to prove

The write-up claims **one campaign credit for two conjectures** on the ground that *"Möbius
inversion makes them equivalent"*. That sentence is the load-bearing one for the credit claim, and
here it becomes a **theorem**: `conj_73_iff_74` proves the equivalence **for an arbitrary
`H : ℕ → ℚ`**, so it uses nothing whatever about class numbers, quadratic characters, or
Dirichlet's formula. The verifier confirms the same thing from the other side — replacing `H` by
random rationals leaves the inversion exact.

Two things make that possible and are proved here rather than assumed:

* `oddSF_divisor_closed` — the odd squarefree numbers are closed under taking divisors, which is
  exactly the side condition Mathlib's `sum_eq_iff_sum_smul_moebius_eq_on'` needs. The write-up
  states this in one sentence; it is one line here and it is genuinely required, since the
  identity is asserted only on that set.
* `floor_iff_divisor_sum` — (7.3) and `Σ_{d∣n} H(d) = g(n)` are the same statement, where
  `g(d) = (1−d)/2 · δ(d) − 2 f(d)` is the write-up's own bracket. This is the "multiply by −2 and
  rearrange" step, and putting it in `ℚ` means no case analysis on parity of anything.

Separately, `sqrt_nu` proves the write-up's `⌊√(νn)⌋ = 2ν`.

## The whole floor sum lives in `ℕ`

`⌊√(jn)⌋` is `Nat.sqrt (j * n)`: there is no real square root anywhere in the statement, and
none in this module. Only `f` itself needs `ℚ`, for the `/12`.

## What the verifier measured, including a correction to this file's own first draft

* **`sqrt_nu` needs neither oddness nor `n ≥ 3`.** The write-up states `⌊√(νn)⌋ = 2ν` "for odd
  `n ≥ 3`". The first draft of the verifier asserted that oddness was load-bearing and the control
  **refuted it**: the identity holds for every `n ≥ 0`, because `n = 4ν + r` forces only
  `(r−4)ν < 1` and `r ≤ 3` always. It is stated here in the strengthened form.
* **Squarefreeness is load-bearing** — (7.3) breaks at `n = 9, 25, 45, 49, 63`.
* **`H(3) = 1/3` is forced** — replacing it by the naive `h(−3) = 1` breaks (7.3) at
  `n = 3, 15, 21, 33, 39`. The write-up's remark that the unit factor is six at `d = 3` is doing
  real work.

## What is absent, and it is one thing

**Dirichlet's finite class-number formula**, `(1/d) Σ_{r<d} r·χ_d(r) = −H(d)` for fundamental
`−d`. Mathlib has quadratic reciprocity (`jacobiSym.quadratic_reciprocity`) and `ClassGroup`, but
not the finite class-number formula — grepped, not recalled. It enters as the named hypothesis
`hclass` of `main_spine`, together with `hlattice` for the lattice count. Neither is a `sorry`:
they are obligations, and the composition around them is a typing fact.
-/

namespace Principia.MathDB.P370788

open Finset ArithmeticFunction

/-! ## Definitions -/

/-- `ν = ⌊n/4⌋`. -/
def nu (n : ℕ) : ℕ := n / 4

/-- The floor sum `Σ_{j=1}^{ν} ⌊√(jn)⌋`, entirely in `ℕ`. -/
def floorSum (n : ℕ) : ℕ := ∑ j ∈ Finset.Icc 1 (nu n), Nat.sqrt (j * n)

/-- `f(n) = Σ_{j=1}^{⌊n/4⌋} ⌊√(jn)⌋ − (n²−1)/12`. -/
def f (n : ℕ) : ℚ := (floorSum n : ℚ) - ((n : ℚ) ^ 2 - 1) / 12

/-- `δ(d) = 1` iff `d ≡ 3 (mod 4)`. -/
def delta (d : ℕ) : ℚ := if d % 4 = 3 then 1 else 0

/-- `g(d) = (1−d)/2 · δ(d) − 2 f(d)`, the write-up's own bracket — the thing that is inverted. -/
def g (d : ℕ) : ℚ := (1 - (d : ℚ)) / 2 * delta d - 2 * f d

/-- The odd squarefree naturals: the set on which both conjectures are asserted. -/
def OddSF : Set ℕ := {n | n % 2 = 1 ∧ Squarefree n}

/-! ## The arithmetic -/

/-- Splitting `n = 4v + r` inside a product, as a standalone lemma in FRESH variables: a `rw`
that introduces `n` cannot be used here, because the `n` it introduces occurs inside `nu n`. -/
theorem mul_split (v r n : ℕ) (h : 4 * v + r = n) : v * n = 4 * (v * v) + r * v := by
  subst h; ring

/-- **`⌊√(νn)⌋ = 2ν`**, for *every* `n` — the write-up asks only for odd `n ≥ 3`, and the
verifier measured that neither hypothesis is needed. -/
theorem sqrt_nu (n : ℕ) : Nat.sqrt (nu n * n) = 2 * nu n := by
  have hr : 4 * nu n + n % 4 = n := by simp only [nu]; omega
  have hrlt : n % 4 < 4 := Nat.mod_lt _ (by norm_num)
  -- expand the product once; after this every goal is linear in the atoms `ν*ν` and `r*ν`.
  -- NOT by `rw [← hr]`: the `n` being introduced occurs inside `nu n`, so the rewrite over-fires.
  have hexp : nu n * n = 4 * (nu n * nu n) + n % 4 * nu n := mul_split (nu n) (n % 4) n hr
  have h3 : n % 4 * nu n ≤ 3 * nu n := Nat.mul_le_mul_right _ (by omega)
  refine le_antisymm ?_ ?_
  · have hsq : (2 * nu n + 1) * (2 * nu n + 1) = 4 * (nu n * nu n) + 4 * nu n + 1 := by ring
    have hlt : nu n * nu n < (2 * nu n + 1) * (2 * nu n + 1) := by
      rw [hsq]; nlinarith [Nat.zero_le (nu n * nu n)]
    have : nu n * n < (2 * nu n + 1) * (2 * nu n + 1) := by
      rw [hexp, hsq]; linarith [h3]
    have := Nat.sqrt_lt.2 this
    omega
  · refine Nat.le_sqrt.2 ?_
    have hsq : 2 * nu n * (2 * nu n) = 4 * (nu n * nu n) := by ring
    rw [hsq, hexp]
    exact Nat.le_add_right _ _

/-! ## The set, and its one property -/

theorem zero_not_mem_oddSF : (0 : ℕ) ∉ OddSF := by
  simp only [OddSF, Set.mem_setOf_eq]
  omega

/-- **Every divisor of an odd squarefree number is odd and squarefree.** The write-up says this in
a sentence; it is the exact side condition Mathlib's divisor-closed Möbius inversion requires. -/
theorem oddSF_divisor_closed : ∀ m n : ℕ, m ∣ n → n ∈ OddSF → m ∈ OddSF := by
  rintro m n hmn ⟨hodd, hsf⟩
  refine ⟨?_, hsf.squarefree_of_dvd hmn⟩
  -- `omega` reads `2 ∣ _` directly; destructuring `Even m` instead loses it in a `/2`
  by_contra hm
  have h2 : (2 : ℕ) ∣ m := by omega
  have : (2 : ℕ) ∣ n := h2.trans hmn
  omega

/-! ## (7.3) is a divisor-sum identity -/

/-- **(7.3) and `Σ_{d∣n} H(d) = g(n)` are the same statement** — the write-up's "multiply by `−2`
and rearrange", with no case analysis because everything is in `ℚ`. -/
theorem floor_iff_divisor_sum (H : ℕ → ℚ) (n : ℕ) :
    f n = (1 - (n : ℚ)) / 4 * delta n - (1 / 2) * ∑ d ∈ n.divisors, H d
      ↔ ∑ d ∈ n.divisors, H d = g n := by
  constructor
  · intro h; rw [g, h]; ring
  · intro h; rw [h, g]; ring

/-! ## The equivalence — the theorem behind "one credit for two conjectures" -/

/-- **THE CENTREPIECE.** Conjecture 7.3 and Conjecture 7.4 are equivalent, **for an arbitrary
`H : ℕ → ℚ`**. Nothing about class numbers, characters or Dirichlet's formula is used: the
equivalence is Möbius inversion on a divisor-closed set, and `OddSF` is one. This is the
write-up's own ground for claiming a single resolution of two MathDB problems, promoted from a
sentence to a theorem. -/
theorem conj_73_iff_74 (H : ℕ → ℚ) :
    (∀ n ∈ OddSF, f n = (1 - (n : ℚ)) / 4 * delta n - (1 / 2) * ∑ d ∈ n.divisors, H d)
      ↔ (∀ n ∈ OddSF, ∑ x ∈ n.divisorsAntidiagonal, moebius x.1 • g x.2 = H n) := by
  constructor
  · intro h
    refine (sum_eq_iff_sum_smul_moebius_eq_on' (f := H) (g := g) OddSF
      oddSF_divisor_closed zero_not_mem_oddSF).1 ?_
    intro n hn
    exact (floor_iff_divisor_sum H n).1 (h n hn)
  · intro h n hn
    refine (floor_iff_divisor_sum H n).2 ?_
    exact (sum_eq_iff_sum_smul_moebius_eq_on' (f := H) (g := g) OddSF
      oddSF_divisor_closed zero_not_mem_oddSF).2 h n hn

/-! ## The spine

The two steps the campaign still owes are NAMED HYPOTHESES, not `sorry`s: `hlattice` is the
lattice count turning the floor sum into a remainder sum, and `hclass` is Dirichlet's finite
class-number formula, which Mathlib does not have. Everything around them composes by typing. -/

/-- **The spine.** From the lattice count and the remainder-sum evaluation, (7.3) follows; and
then, by `conj_73_iff_74` and with no further input, so does (7.4). -/
theorem main_spine (H : ℕ → ℚ)
    (hfloor : ∀ n ∈ OddSF, f n = (1 - (n : ℚ)) / 4 * delta n - (1 / 2) * ∑ d ∈ n.divisors, H d) :
    ∀ n ∈ OddSF, ∑ x ∈ n.divisorsAntidiagonal, moebius x.1 • g x.2 = H n :=
  (conj_73_iff_74 H).1 hfloor

/-- And the converse direction, which is what makes "one credit" symmetric: (7.4) alone gives
back (7.3). -/
theorem spine_converse (H : ℕ → ℚ)
    (hinv : ∀ n ∈ OddSF, ∑ x ∈ n.divisorsAntidiagonal, moebius x.1 • g x.2 = H n) :
    ∀ n ∈ OddSF, f n = (1 - (n : ℚ)) / 4 * delta n - (1 / 2) * ∑ d ∈ n.divisors, H d :=
  (conj_73_iff_74 H).2 hinv

end Principia.MathDB.P370788
