import Mathlib

set_option autoImplicit false

/-!
# MathDB #374965 — bivariate Ehrhart reciprocity for preorder polytopes (SPINE)

Write-up `mathdb-open-problems/problems/374965/solution.tex` on the `mathdb-results` branch of
`antoshashakov/Principia-Math-In-Progress`.
Source: C. A. Athanasiadis and F. Chapoton, *Polytopes and posets associated to preorders*
(arXiv:2605.26916v1), **Conjecture 7.2**.

For a preorder `τ` on a finite set `E` with `|E| = n`, Athanasiadis–Chapoton form the
two-parameter polytope `Q τ r s = r·∑_e Δ_{U(e)} + s·Δ_E`, show (Prop. 3.3) that it is cut out
by

    x e ≥ 0   (e ∈ E),        ∑_{e ∈ I} x e ≤ r·|I| + s   (I a nonempty order ideal),

and show (Prop. 7.1) that `#(Q τ r s ∩ ℤ^E)` is a polynomial `E_τ(u,v)` of total degree `n`.
Conjecture 7.2 asserts

    E_τ(-u,-v) = (-1)^n · E_τ(u-1, v-1).

## What is proved here, and what is carried

The write-up's proof has three ingredients, and **the two it contributes are proved outright
below**; the one carried is the classical theorem it quotes.

**Proved outright, and both are consumed by `reciprocity`.**

* `bijOn_sub_one` / `strictCard_eq` — **the translation lemma, the write-up's actual
  contribution.** Subtracting the all-ones vector is a bijection from the *strict* solutions at
  `(r, s)` onto the solutions at `(r-1, s-1)`. Over `ℤ` strictness is `1 ≤ x e` and
  `∑ ≤ r|I| + s - 1`, and `y = x - 1` carries each constraint to the corresponding one at
  `(r-1, s-1)` **because the `I`-th constraint has coefficient `1` on exactly `|I|`
  coordinates** -- the mechanism is the identity `∑_{e ∈ I} 1 = |I|`, not anything geometric.
  Two strengthenings over the write-up: `ideals` is an ARBITRARY family of `Finset E` (that its
  members are order ideals is never used), and the conclusion is a `Set.BijOn`, so injectivity
  and surjectivity are both discharged rather than only the stated inclusion.
* `eq_zero_of_eval_pos_nat` — **the extension from positive integers to all arguments.** A
  two-variable polynomial over `ℚ` vanishing at every pair of positive integers is identically
  zero. The write-up spends four lines here; it is the step that turns finitely-meaningful
  counting identities into the polynomial identity actually conjectured. Proved by
  `Polynomial.eq_zero_of_infinite_isRoot` in each variable in turn.

**Carried** (`AC`, one named hypothesis bundling what the write-up quotes):

* `counts` — AC Prop. 7.1 together with Prop. 3.3: at nonnegative integers the polynomial's
  value is the number of integral points, which are the solutions of the system.
* `reciprocity_interior` — **Ehrhart–Macdonald reciprocity**, already specialised along the ray
  and combined with the identification of integral interior points with strict solutions (which
  the write-up derives from full-dimensionality, `Q ⊇ [0,r]^E`). **Mathlib has no Ehrhart theory
  whatsoever** -- no Ehrhart polynomial, no reciprocity, no Macdonald -- so this is a missing
  chapter rather than a gap more work would close. Carrying it is the honest encoding.
* `diff_poly` — that the two sides' difference is given by a polynomial in the two arguments.
  Substituting `-u` and `u-1` into a `Polynomial (Polynomial ℚ)` is routine algebra but the
  Mathlib plumbing for bivariate substitution is not, and nothing mathematical hinges on it.

`AC` is a hypothesis on opaque data, never an `axiom`, so it adds nothing to any footprint, and
`reciprocity` carries it in its own signature.

No claim is made about AC's descent formula (Remark 7.3), nor about the five-element example
their own verifier checks.
-/

namespace Principia.MathDB.P374965

open Finset

variable {E : Type*} [Fintype E] [DecidableEq E]

/-! ### The lattice-point sets -/

/-- The integral points of `Q τ r s`: the solutions of AC's system (eq:ineq). -/
def sols (ideals : Finset (Finset E)) (r s : ℤ) : Set (E → ℤ) :=
  {x | (∀ e, 0 ≤ x e) ∧ ∀ I ∈ ideals, ∑ e ∈ I, x e ≤ r * I.card + s}

/-- The integral points satisfying every inequality STRICTLY. Over `ℤ`, `0 < x e ↔ 1 ≤ x e` and
`∑ < r|I| + s ↔ ∑ ≤ r|I| + s - 1`. -/
def strictSols (ideals : Finset (Finset E)) (r s : ℤ) : Set (E → ℤ) :=
  {x | (∀ e, 1 ≤ x e) ∧ ∀ I ∈ ideals, ∑ e ∈ I, x e ≤ r * I.card + s - 1}

/-- The all-ones vector. -/
def one' (E : Type*) : E → ℤ := fun _ => 1

theorem sum_one' (I : Finset E) : ∑ e ∈ I, one' E e = (I.card : ℤ) := by
  simp [one']

/-! ### The translation lemma, proved outright -/

/-- Membership in `strictSols r s` is membership of the translate in `sols (r-1) (s-1)`: the
computation is `∑_{e ∈ I} (x e - 1) = ∑_{e ∈ I} x e - |I|`, moving the `I`-th bound from
`r|I| + s - 1` to `(r-1)|I| + (s-1)`. -/
theorem mem_strict_iff_sub_one_mem (ideals : Finset (Finset E)) (r s : ℤ) (x : E → ℤ) :
    x ∈ strictSols ideals r s ↔ (x - one' E) ∈ sols ideals (r - 1) (s - 1) := by
  have hsum : ∀ I : Finset E, ∑ e ∈ I, (x - one' E) e = (∑ e ∈ I, x e) - (I.card : ℤ) := by
    intro I
    simp [Finset.sum_sub_distrib, sum_one']
  have hexp : ∀ I : Finset E,
      (r - 1) * (I.card : ℤ) + (s - 1) = (r * (I.card : ℤ) + s - 1) - (I.card : ℤ) := by
    intro I; ring
  constructor
  · rintro ⟨hpos, hbound⟩
    refine ⟨fun e => ?_, ?_⟩
    · have := hpos e
      simp only [Pi.sub_apply, one']
      omega
    · intro I hI
      have h := hbound I hI
      rw [hsum I, hexp I]
      omega
  · rintro ⟨hpos, hbound⟩
    refine ⟨fun e => ?_, ?_⟩
    · have := hpos e
      simp only [Pi.sub_apply, one'] at this
      omega
    · intro I hI
      have h := hbound I hI
      rw [hsum I, hexp I] at h
      omega

/-- **The translation lemma.** `x ↦ x - 1` is a bijection from the strict solutions at `(r,s)`
onto the solutions at `(r-1, s-1)`. -/
theorem bijOn_sub_one (ideals : Finset (Finset E)) (r s : ℤ) :
    Set.BijOn (fun x : E → ℤ => x - one' E)
      (strictSols ideals r s) (sols ideals (r - 1) (s - 1)) := by
  refine ⟨fun x hx => (mem_strict_iff_sub_one_mem ideals r s x).mp hx, ?_, ?_⟩
  · intro a _ b _ hab
    -- `hab` is beta-reduced in the goal, so give it its reduced type and cancel.
    have hab' : a - one' E = b - one' E := hab
    exact sub_left_inj.mp hab'
  · intro y hy
    refine ⟨y + one' E, ?_, by simp⟩
    refine (mem_strict_iff_sub_one_mem ideals r s (y + one' E)).mpr ?_
    have h : (y + one' E) - one' E = y := by simp
    rw [h]; exact hy

/-- The cardinality form, which is what the reciprocity argument consumes. -/
theorem strictCard_eq (ideals : Finset (Finset E)) (r s : ℤ) :
    Nat.card (strictSols ideals r s) = Nat.card (sols ideals (r - 1) (s - 1)) :=
  Nat.card_congr (Set.BijOn.equiv _ (bijOn_sub_one ideals r s))

/-! ### The extension to a polynomial identity, proved outright

The bivariate polynomial is carried as `Polynomial (Polynomial ℚ)` -- a polynomial in the first
argument whose coefficients are polynomials in the second -- which is the shape the write-up's
argument uses. `biEval p u v` is its value at `(u, v)`. -/

/-- Evaluation of a bivariate polynomial at `(u, v)`. `noncomputable` because
`Polynomial.map` is. -/
noncomputable def biEval (p : Polynomial (Polynomial ℚ)) (u v : ℚ) : ℚ :=
  (p.map (Polynomial.evalRingHom v)).eval u

/-- A one-variable rational polynomial vanishing at every positive integer is zero: the
positive integers are an infinite set of roots. -/
theorem eq_zero_of_eval_pos_nat_one (p : Polynomial ℚ)
    (h : ∀ k : ℕ, 0 < k → p.eval (k : ℚ) = 0) : p = 0 := by
  apply Polynomial.eq_zero_of_infinite_isRoot
  have hinj : Function.Injective (fun k : ℕ => ((k + 1 : ℕ) : ℚ)) := by
    intro a b hab
    have : ((a + 1 : ℕ) : ℚ) = ((b + 1 : ℕ) : ℚ) := hab
    exact Nat.succ_injective (Nat.cast_injective this)
  have hsub : (Set.range fun k : ℕ => ((k + 1 : ℕ) : ℚ)) ⊆ {x | p.IsRoot x} := by
    rintro x ⟨k, rfl⟩
    exact h (k + 1) (Nat.succ_pos k)
  exact Set.Infinite.mono hsub (Set.infinite_range_of_injective hinj)

/-- **The extension step.** A bivariate polynomial over `ℚ` vanishing at every pair of positive
integers is identically zero. For each fixed positive second argument the specialisation
vanishes at all positive integers, hence is zero, hence every coefficient -- itself a
polynomial -- vanishes at all positive integers and is zero. -/
theorem eq_zero_of_eval_pos_nat (p : Polynomial (Polynomial ℚ))
    (h : ∀ r t : ℕ, 0 < r → 0 < t → biEval p (r : ℚ) (t : ℚ) = 0) : p = 0 := by
  have hcoeff : ∀ i, p.coeff i = 0 := by
    intro i
    refine eq_zero_of_eval_pos_nat_one _ ?_
    intro t ht
    have hzero : p.map (Polynomial.evalRingHom (t : ℚ)) = 0 :=
      eq_zero_of_eval_pos_nat_one _ (fun r hr => h r t hr ht)
    have hci : (p.map (Polynomial.evalRingHom (t : ℚ))).coeff i = 0 := by
      rw [hzero]; simp
    simpa [Polynomial.coeff_map] using hci
  exact Polynomial.ext fun i => by rw [hcoeff i]; simp

/-! ### The carried classical input, and the theorem -/

/-- What the write-up quotes: AC Prop. 3.3 + Prop. 7.1, Ehrhart–Macdonald reciprocity already
specialised along the ray and combined with the interior/strict identification, and the routine
fact that the two sides' difference is polynomial. NOT proved here -- Mathlib has no Ehrhart
theory. -/
structure AC (E : Type*) [Fintype E] [DecidableEq E]
    (ideals : Finset (Finset E)) (Epoly diff : Polynomial (Polynomial ℚ)) : Prop where
  /-- AC Prop. 7.1 with Prop. 3.3: at nonnegative integers the polynomial counts the solutions
  of the inequality system. -/
  counts : ∀ r s : ℕ, biEval Epoly (r : ℚ) (s : ℚ)
    = (Nat.card (sols ideals (r : ℤ) (s : ℤ)) : ℚ)
  /-- Ehrhart–Macdonald reciprocity, in terms of the STRICT solutions -- the integral interior
  points. This is the step whose output the translation lemma rewrites. -/
  reciprocity_interior : ∀ r s : ℕ, 0 < r → 0 < s →
    biEval Epoly (-(r : ℚ)) (-(s : ℚ))
      = (-1 : ℚ) ^ (Fintype.card E) * (Nat.card (strictSols ideals (r : ℤ) (s : ℤ)) : ℚ)
  /-- The two sides of the conjecture differ by the value of a polynomial. -/
  diff_poly : ∀ u v : ℚ,
    biEval diff u v
      = biEval Epoly (-u) (-v) - (-1 : ℚ) ^ (Fintype.card E) * biEval Epoly (u - 1) (v - 1)

/-- **MathDB #374965 / Athanasiadis–Chapoton Conjecture 7.2.**
`E_τ(-u,-v) = (-1)^n · E_τ(u-1, v-1)` at every rational pair, which for polynomials is the
identity conjectured.

The proof is the write-up's: reciprocity gives the identity at positive integers in terms of
interior points, `strictCard_eq` (the translation lemma) rewrites that count as the count at
`(r-1, s-1)`, `counts` turns it back into a value of the polynomial, and
`eq_zero_of_eval_pos_nat` extends from positive integers to everything. Conditional on `AC`. -/
theorem reciprocity {ideals : Finset (Finset E)} {Epoly diff : Polynomial (Polynomial ℚ)}
    (hac : AC E ideals Epoly diff) (u v : ℚ) :
    biEval Epoly (-u) (-v)
      = (-1 : ℚ) ^ (Fintype.card E) * biEval Epoly (u - 1) (v - 1) := by
  have hzero : diff = 0 := by
    refine eq_zero_of_eval_pos_nat _ ?_
    intro r t hr ht
    -- reciprocity at `(r, t)`, then the translation lemma, then `counts` at `(r-1, t-1)`
    have h1 := hac.reciprocity_interior r t hr ht
    have h2 : Nat.card (strictSols ideals (r : ℤ) (t : ℤ))
        = Nat.card (sols ideals ((r : ℤ) - 1) ((t : ℤ) - 1)) := strictCard_eq ideals _ _
    obtain ⟨r', hr'⟩ : ∃ r' : ℕ, r = r' + 1 := ⟨r - 1, by omega⟩
    obtain ⟨t', ht'⟩ : ∃ t' : ℕ, t = t' + 1 := ⟨t - 1, by omega⟩
    have hrz : ((r : ℤ) - 1) = (r' : ℤ) := by rw [hr']; push_cast; ring
    have htz : ((t : ℤ) - 1) = (t' : ℤ) := by rw [ht']; push_cast; ring
    have h3 := hac.counts r' t'
    have hru : ((r : ℚ) - 1) = (r' : ℚ) := by rw [hr']; push_cast; ring
    have htu : ((t : ℚ) - 1) = (t' : ℚ) := by rw [ht']; push_cast; ring
    rw [hac.diff_poly, h1, h2, hrz, htz, hru, htu, h3]
    ring
  have hd := hac.diff_poly u v
  rw [hzero] at hd
  have h0 : biEval (0 : Polynomial (Polynomial ℚ)) u v = 0 := by
    simp [biEval]
  rw [h0] at hd
  -- `linarith` cannot finish here: `(-1)^n * biEval …` is a product of two unknowns, which it
  -- reads as nonlinear. Cancelling the subtraction directly avoids the issue entirely.
  exact sub_eq_zero.mp hd.symm

end Principia.MathDB.P374965
