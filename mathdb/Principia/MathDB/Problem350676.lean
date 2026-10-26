import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

/-!
# MathDB #350676 -- branched simplicial fans satisfy the gradient-Laplacian identity

Write-up `mathdb-open-problems/problems/350676/solution.tex`,
*Branched simplicial fans satisfy the gradient-Laplacian identity*, 22 September 2026.
Source: Contreras--Tawfeek, current preprint, **Conjecture 1**: with `B = boundary_d`,
`Delta_d = B B^T`, `m = |K_d|` and `n = |K_{d-1}|`,

  `det(Delta_d + lambda I_n) = sum_{i} |M_{m-i}(K)| lambda^{n-i}`      (1)

holds **if and only if** `K` is an orientable pseudomanifold.

**The witness** is `K(2,3)`: the complex with facets `012`, `013`, `014` -- three triangles
glued along the common edge `{0,1}`.  It is not a pseudomanifold, since that edge lies in
THREE facets, yet both sides of (1) equal `lambda^4 (lambda+2)^2 (lambda+5)`.

**What is proved here.**

* `matching_sum` -- the write-up's general matching-count identity, for EVERY `r` and `d`
  over any commutative ring: `sum_i C(r,i)(d^i + i d^(i-1)) lambda^(r-i)
  = (lambda+d)^r + r (lambda+d)^(r-1)`.  Its two halves are the binomial theorem and its
  `d`-derivative, the latter run through `(j+1) C(r+1,j+1) = (r+1) C(r,j)`.
* `det_lapPlus` -- the determinant side for `K(2,3)`, as a genuine `Matrix.det` of the
  explicit `7 x 7` matrix `Delta_2 + lambda I` with `lambda` a free real, equal to
  `lambda^4 (lambda+2)^2 (lambda+5)`.
* `identity_holds` -- hence (1) holds for `K(2,3)`.
* `not_ridge` and `not_conj` -- the edge `{0,1}` lies in three facets, so `K` fails the
  ridge condition every pseudomanifold satisfies, and Conjecture 1's "only if" half is
  false.  Using the ridge condition in place of "orientable pseudomanifold" makes the
  conjecture WEAKER (it is a necessary condition), so the refutation is stronger.

**The coefficients are COMPUTED, not carried (2026-09-23).**  `|M_j(K)|` is the set of
ACYCLIC matchings of size `i` in the top two levels of the Hasse diagram.  For `K(2,3)` that
is a matching count on a bipartite graph with three facets and seven ridges, so there are
only `8^3 = 512` partial assignments of a ridge to each facet and the whole question is
decidable:

* `matchCount_eq` -- the plain matching counts are `1, 9, 24, 20`, by `decide`.
* `all_matchings_acyclic` -- NO matching has a discrete-Morse cycle.  In the top two levels
  a cycle is an alternating closed walk, which on matched facets is the relation "G is
  matched, its ridge is a face of F, and it differs from F's ridge"; with three facets,
  powers up to three settle it.  The reason is visible in `incB`: the three facets pairwise
  share only the ridge `01`, so a two-step walk would have to use it twice.
* `acyclic_counts` and `gradPoly_eq_acyclic` -- hence `gradPoly` IS `sum_i |M_{3-i}(K)|
  lambda^(7-i)` with the source's own definition of `M`, and nothing about the right-hand
  side of (1) is assumed.

An earlier note claimed `|M_j|` "cannot be computed inside Lean" because Mathlib has no
discrete Morse theory.  That conflated the write-up's GENERAL derivation of formula (3),
which does use discrete Morse theory for every `(d, r)`, with the single finite instance the
refutation needs.  The general formula (2) is still not formalized -- only the instance.

**Upstream status.**  The collaborator's own state is
`full-counterexample-eligibility-pending`, and their abstract records that the identified
journal final remains unread.  Nothing certified here depends on that audit.

Values checked first in `Campaigns/MathDB-Formalization/verify_350676.py`, which builds the
boundary matrix from the facets, confirms `B^T B = d I_r + J_r`, computes the characteristic
polynomial symbolically, and checks the general matching identity for `r <= 6`.
-/

namespace Principia.MathDB.P350676

open Finset

variable {R : Type*} [CommRing R]

/-- The binomial theorem in the shape the matching count uses. -/
theorem half_plain (lam d : R) (r : ℕ) :
    ∑ i ∈ range (r + 1), (Nat.choose r i : R) * d ^ i * lam ^ (r - i) = (lam + d) ^ r := by
  have h := add_pow d lam r
  rw [add_comm d lam] at h
  rw [h]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- The derivative half: `∑ C(r,i) i d^{i-1} λ^{r-i} = r (λ+d)^{r-1}`. -/
theorem half_deriv (lam d : R) (r : ℕ) :
    ∑ i ∈ range (r + 1), (Nat.choose r i : R) * ((i : R) * d ^ (i - 1)) * lam ^ (r - i)
      = (r : R) * (lam + d) ^ (r - 1) := by
  cases r with
  | zero => simp
  | succ r =>
      rw [Finset.sum_range_succ']
      simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero]
      have hstep : ∀ j ∈ range (r + 1),
          (Nat.choose (r + 1) (j + 1) : R) * (((j + 1 : ℕ) : R) * d ^ (j + 1 - 1))
              * lam ^ (r + 1 - (j + 1))
            = ((r : R) + 1) * ((Nat.choose r j : R) * d ^ j * lam ^ (r - j)) := by
        intro j _
        have hc : ((r + 1) * Nat.choose r j : ℕ)
            = (Nat.choose (r + 1) (j + 1) * (j + 1) : ℕ) := Nat.add_one_mul_choose_eq r j
        have hR : ((r : R) + 1) * (Nat.choose r j : R)
            = (Nat.choose (r + 1) (j + 1) : R) * ((j : R) + 1) := by
          exact_mod_cast congrArg (fun n : ℕ => (n : R)) hc
        rw [show r + 1 - (j + 1) = r - j from by omega, show j + 1 - 1 = j from by omega]
        push_cast
        linear_combination (-(d ^ j * lam ^ (r - j))) * hR
      rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum, half_plain]
      push_cast
      ring_nf

/-- **The write-up's matching-count identity.**  With `|M_{r-i}| = C(r,i)(d^i + i d^{i-1})`
for `1 ≤ i ≤ r` and `|M_r| = 1`, the gradient generating polynomial telescopes. -/
theorem matching_sum (lam d : R) (r : ℕ) :
    ∑ i ∈ range (r + 1),
        (Nat.choose r i : R) * (d ^ i + (i : R) * d ^ (i - 1)) * lam ^ (r - i)
      = (lam + d) ^ r + (r : R) * (lam + d) ^ (r - 1) := by
  have h : ∀ i ∈ range (r + 1),
      (Nat.choose r i : R) * (d ^ i + (i : R) * d ^ (i - 1)) * lam ^ (r - i)
        = (Nat.choose r i : R) * d ^ i * lam ^ (r - i)
          + (Nat.choose r i : R) * ((i : R) * d ^ (i - 1)) * lam ^ (r - i) := by
    intro i _; ring
  rw [Finset.sum_congr rfl h, Finset.sum_add_distrib, half_plain, half_deriv]

/-! ### The explicit witness `K(2,3)`: facets `012`, `013`, `014` -/

/-- The facets of the write-up's five-vertex example. -/
def facets : List (Finset ℕ) := [{0, 1, 2}, {0, 1, 3}, {0, 1, 4}]

/-- **`K` is not a pseudomanifold**: the face `{0,1}` lies in all three facets, while a
pseudomanifold requires exactly two (and a pseudomanifold with boundary, at most two). -/
theorem not_pseudomanifold :
    (facets.filter (fun F => ({0, 1} : Finset ℕ) ⊆ F)).length = 3 := by
  decide

/-- The write-up's matching counts at `d = 2`, `r = 3`, from formula (3). -/
theorem matching_counts :
    (Nat.choose 3 0 : ℕ) * (2 ^ 0 + 0 * 2 ^ 0) = 1 ∧
    (Nat.choose 3 1 : ℕ) * (2 ^ 1 + 1 * 2 ^ 0) = 9 ∧
    (Nat.choose 3 2 : ℕ) * (2 ^ 2 + 2 * 2 ^ 1) = 24 ∧
    (Nat.choose 3 3 : ℕ) * (2 ^ 3 + 3 * 2 ^ 2) = 20 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- The gradient generating polynomial of `K(2,3)`, from those counts. -/
theorem gradient_poly (lam : R) :
    1 * lam ^ 7 + 9 * lam ^ 6 + 24 * lam ^ 5 + 20 * lam ^ 4
      = lam ^ 4 * (lam + 2) ^ 2 * (lam + 5) := by
  ring

/-! ### The boundary Laplacian of `K(2,3)` and the conjecture -/

open Matrix

/-- `Δ₂ + λI` for `K(2,3)`, with edges ordered `01, 02, 12, 03, 13, 04, 14` and the
standard simplicial boundary `∂[a,b,c] = [b,c] - [a,c] + [a,b]`. -/
noncomputable def lapPlus (l : ℝ) : Matrix (Fin 7) (Fin 7) ℝ :=
  !![l+3, -1, 1, -1, 1, -1, 1;
     -1, l+1, -1, 0, 0, 0, 0;
     1, -1, l+1, 0, 0, 0, 0;
     -1, 0, 0, l+1, -1, 0, 0;
     1, 0, 0, -1, l+1, 0, 0;
     -1, 0, 0, 0, 0, l+1, -1;
     1, 0, 0, 0, 0, -1, l+1]

/-- The gradient generating polynomial `∑ᵢ |M_{m-i}(K)| λ^{n-i}` of `K(2,3)`, whose
coefficients `1, 9, 24, 20` are the write-up's formula (3) at `d = 2`, `r = 3`. -/
noncomputable def gradPoly (l : ℝ) : ℝ := 1 * l^7 + 9 * l^6 + 24 * l^5 + 20 * l^4

set_option maxHeartbeats 4000000 in
/-- **The determinant side.** -/
theorem det_lapPlus (l : ℝ) : (lapPlus l).det = l^4 * (l+2)^2 * (l+5) := by
  rw [lapPlus]
  simp [Matrix.det_succ_row_zero (n := 6), Matrix.det_succ_row_zero (n := 5),
    Matrix.det_succ_row_zero (n := 4), Matrix.det_succ_row_zero (n := 3), Fin.succAbove,
    Matrix.det_fin_three, Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]
  ring

/-- **The source's identity (1) HOLDS for `K(2,3)`** -- both sides are
`λ⁴(λ+2)²(λ+5)`. -/
theorem identity_holds (l : ℝ) : (lapPlus l).det = gradPoly l := by
  rw [det_lapPlus, gradPoly, gradient_poly]

/-! ### The matching counts, COMPUTED rather than carried

`ℳ_{m-i}(K)` is the set of acyclic matchings of size `i` in the top two levels of the Hasse
diagram.  For `K(2,3)` the write-up proves every matching there IS acyclic, because the
bipartite incidence graph is a TREE — one central ridge `{0,1}` joined to the three facets,
each carrying two further ridges of its own.  Granting that, `|ℳ_{3-i}|` is an ordinary
finite matching count, and a finite matching count is DECIDABLE: there are only `8³ = 512`
partial assignments of a ridge to each facet.  So the coefficients `1, 9, 24, 20` need not be
taken from formula (3) on trust. -/

set_option maxRecDepth 8000

/-- Incidence of the three facets with the seven ridges, in the order
`01, 02, 12, 03, 13, 04, 14`: facet `012` meets `01,02,12`, facet `013` meets `01,03,13`,
facet `014` meets `01,04,14`. -/
def incB (f : Fin 3) (r : Fin 7) : Bool :=
  if f = 0 then r == 0 || r == 1 || r == 2
  else if f = 1 then r == 0 || r == 3 || r == 4
  else r == 0 || r == 5 || r == 6

/-- A partial assignment of a ridge to each of the three facets. -/
abbrev PM := Option (Fin 7) × Option (Fin 7) × Option (Fin 7)

def ridgeOpts : List (Option (Fin 7)) :=
  [none, some 0, some 1, some 2, some 3, some 4, some 5, some 6]

def allPM : List PM :=
  ridgeOpts.flatMap fun a => ridgeOpts.flatMap fun b => ridgeOpts.map fun c => (a, b, c)

def okAt (f : Fin 3) : Option (Fin 7) → Bool
  | none => true
  | some r => incB f r

def distOpt : Option (Fin 7) → Option (Fin 7) → Bool
  | some a, some b => !(a == b)
  | _, _ => true

/-- A matching: every assigned ridge is incident to its facet, and no ridge is used twice. -/
def isMatching (t : PM) : Bool :=
  okAt 0 t.1 && okAt 1 t.2.1 && okAt 2 t.2.2
    && distOpt t.1 t.2.1 && distOpt t.1 t.2.2 && distOpt t.2.1 t.2.2

def pmSize (t : PM) : ℕ :=
  (if t.1.isSome then 1 else 0) + (if t.2.1.isSome then 1 else 0)
    + (if t.2.2.isSome then 1 else 0)

/-- The number of matchings of size `i` in the top two levels of `K(2,3)`. -/
def matchCount (i : ℕ) : ℕ := (allPM.filter (fun t => isMatching t && pmSize t == i)).length

/-- **The matching counts, computed.**  This is the step the row previously CARRIED. -/
theorem matchCount_eq :
    matchCount 0 = 1 ∧ matchCount 1 = 9 ∧ matchCount 2 = 24 ∧ matchCount 3 = 20 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- The computed counts agree with the write-up's formula (3) at `d = 2`, `r = 3`. -/
theorem matchCount_eq_formula :
    matchCount 1 = Nat.choose 3 1 * (2 ^ 1 + 1 * 2 ^ 0) ∧
    matchCount 2 = Nat.choose 3 2 * (2 ^ 2 + 2 * 2 ^ 1) ∧
    matchCount 3 = Nat.choose 3 3 * (2 ^ 3 + 3 * 2 ^ 2) := by
  refine ⟨by decide, by decide, by decide⟩

/-- `gradPoly` really is `∑ᵢ |ℳ_{3-i}(K)| λ^{7-i}` with the COMPUTED counts, so the
conjecture's right-hand side is no longer taken on trust. -/
theorem gradPoly_eq_matchings (l : ℝ) :
    gradPoly l = (matchCount 0 : ℝ) * l ^ 7 + (matchCount 1 : ℝ) * l ^ 6
      + (matchCount 2 : ℝ) * l ^ 5 + (matchCount 3 : ℝ) * l ^ 4 := by
  obtain ⟨h0, h1, h2, h3⟩ := matchCount_eq
  rw [gradPoly, h0, h1, h2, h3]
  norm_num

/-! ### Acyclicity, also decided

`ℳ_j` counts ACYCLIC matchings, so the plain count above is an upper bound until every
matching is known to be acyclic.  In the top two levels a discrete-Morse cycle is an
alternating closed walk `r₁ → F₁ → r₂ → F₂ → … → r₁`, going UP along a matched edge and DOWN
to a different face.  On matched facets that is the relation

  `F ⇒ G  iff  G is matched, its ridge is a face of F, and it differs from F's ridge`,

and a cycle is a closed walk in it.  With only three facets, powers up to three decide the
question, and all `512` assignments can be checked at once. -/

def ridgeOf (t : PM) (f : Fin 3) : Option (Fin 7) :=
  if f = 0 then t.1 else if f = 1 then t.2.1 else t.2.2

/-- The alternating-walk relation on matched facets. -/
def stepB (t : PM) (f g : Fin 3) : Bool :=
  match ridgeOf t f, ridgeOf t g with
  | some rf, some rg => incB f rg && !(rg == rf)
  | _, _ => false

def compB (A B : Fin 3 → Fin 3 → Bool) (i j : Fin 3) : Bool :=
  (A i 0 && B 0 j) || (A i 1 && B 1 j) || (A i 2 && B 2 j)

/-- A closed walk of length `1`, `2` or `3` — with three facets that is every cycle. -/
def hasCycle (t : PM) : Bool :=
  let A := stepB t
  let A2 := compB A A
  let A3 := compB A2 A
  A 0 0 || A 1 1 || A 2 2 || A2 0 0 || A2 1 1 || A2 2 2 || A3 0 0 || A3 1 1 || A3 2 2

/-- **Every matching of the top two levels is acyclic.**  The write-up derives this from the
incidence graph being a tree; here it is decided.  The reason is visible in `incB`: the three
facets pairwise share only the ridge `01`, so a two-step walk would have to use it twice. -/
theorem all_matchings_acyclic :
    (allPM.filter (fun t => isMatching t && hasCycle t)).length = 0 := by decide

/-- The number of ACYCLIC matchings of size `i` — the write-up's `|ℳ_{3-i}(K(2,3))|`. -/
def acyclicMatchCount (i : ℕ) : ℕ :=
  (allPM.filter (fun t => isMatching t && !hasCycle t && pmSize t == i)).length

/-- **The coefficients of the conjecture's right-hand side, with acyclicity included.** -/
theorem acyclic_counts :
    acyclicMatchCount 0 = 1 ∧ acyclicMatchCount 1 = 9 ∧
    acyclicMatchCount 2 = 24 ∧ acyclicMatchCount 3 = 20 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- `gradPoly` is exactly `∑ᵢ |ℳ_{3-i}(K)| λ^{7-i}` — acyclic matchings, as the source
defines them.  Nothing about the right-hand side is now assumed. -/
theorem gradPoly_eq_acyclic (l : ℝ) :
    gradPoly l = (acyclicMatchCount 0 : ℝ) * l ^ 7 + (acyclicMatchCount 1 : ℝ) * l ^ 6
      + (acyclicMatchCount 2 : ℝ) * l ^ 5 + (acyclicMatchCount 3 : ℝ) * l ^ 4 := by
  obtain ⟨h0, h1, h2, h3⟩ := acyclic_counts
  rw [gradPoly, h0, h1, h2, h3]
  norm_num

/-- A pseudomanifold requires every ridge (here every `2`-element face) to lie in exactly
two facets; allowing boundary, in at most two.  This is a NECESSARY condition, so using it
in place of "orientable pseudomanifold" makes the conjecture weaker and the refutation
stronger. -/
def EveryRidgeInAtMostTwo : Prop :=
  ∀ F : Finset ℕ, F.card = 2 → (facets.filter (fun G => F ⊆ G)).length ≤ 2

theorem not_ridge : ¬ EveryRidgeInAtMostTwo := by
  intro h
  have := h {0, 1} (by decide)
  rw [not_pseudomanifold] at this
  omega

/-- Conjecture 1 of Contreras--Tawfeek, "only if" half, for this complex: if the
determinant identity holds then `K` is an orientable pseudomanifold -- in particular every
ridge lies in at most two facets. -/
def Conj : Prop := (∀ l : ℝ, (lapPlus l).det = gradPoly l) → EveryRidgeInAtMostTwo

/-- **Conjecture 1 is false.** -/
theorem not_conj : ¬ Conj := fun h => not_ridge (h identity_holds)

end Principia.MathDB.P350676
