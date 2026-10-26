import Mathlib.Data.List.Basic
import Mathlib.Tactic.NormNum
import Principia.Common.F2LinAlg

set_option autoImplicit false
-- every count below is closed by kernel evaluation over `List Bool`; the default recursion depth
-- is reached while unfolding the 64-element enumeration of the field.
set_option maxRecDepth 100000

/-!
# MathDB #360093 — Aliabadi's Conjecture 38 is FALSE

Write-up: `mathdb-open-problems/problems/360093/solution.tex`, collaborator branch
`mathdb-results` of `antoshashakov/Principia-Math-In-Progress` (enrolled here 2026-09-30).
Source: M. Aliabadi, *Conditions for matchability in groups and field extensions II*,
Discussiones Mathematicae GAA **45** (2025), 135–157, **Conjecture 38** (p. 154); preprint
arXiv:2309.14664v3, Conjecture 5.1.

The conjecture: for finite-dimensional positive-dimensional `K`-subspaces `A, B` of an extension
`L/K`, if `dim_K(aM ∩ A) + dim_K(bM ∩ B) ≤ [M:K] + 1` for all `a, b ∈ L` and all **nontrivial
proper** finite intermediate fields `K ⊊ M ⊊ L`, then `dim_K⟨ST⟩ ≥ dim_K S + dim_K T - 1`.

The counterexample: `K = 𝔽₂`, `L = 𝔽₂[X]/(X⁶+X+1)`, `A = ⟨α,…,α⁵⟩`, `B = ⟨α,α²,α³⟩`. The
hypothesis holds for every scalar pair and both intermediate fields, yet `dim⟨AB⟩ = 6 < 7`.

## The representation, chosen before any Lean was written

An element of `L` is a `List Bool` of length six, `true` in position `j` meaning a coefficient of
`α^j`. Addition is `List.zipWith xor` and multiplication is six shifts with `α⁶ = α + 1` folded
in. The `ℕ`-bitmask encoding is the obvious one and is **unusable**: `Nat.xor` goes through
`Nat.bitwise`, which the kernel cannot accelerate. `native_decide` appears nowhere — it would add
`ofReduceBool` and the campaign gate refuses it. See `Principia.Common.F2LinAlg`.

## Where the hypothesis is checked, and why it is not 8192 kernel evaluations

The write-up checks all `2 · 64² = 8192` scalar-pair instances. In Lean that is the wrong shape:
the left-hand side is a **sum of two independent terms**, so its maximum is the sum of the maxima
and `64 + 64` evaluations per degree suffice. `hyp_two` and `hyp_three` recombine the factored
bounds with `omega`, giving the full `∀ a, ∀ b` statement at a sixty-fourth of the cost. The
verifier checks both forms and their equivalence.

## A finding: containing `1` is not what breaks the hypothesis

The verifier's first negative control predicted that replacing `B` by `⟨1, α, α²⟩` violates the
hypothesis at degree two. It **does not** — that subspace meets `M₂ = {0,1,58,59}` in `{0,1}` only
and the worst sum is exactly the bound. What the hypothesis constrains is how `B` meets the
**translates** of a subfield, nothing else. The control was replaced by a search: of the 1395
three-dimensional `𝔽₂`-subspaces of `L`, **1017 violate the hypothesis** and 378 do not, so the
write-up's `B` is a member of the smaller class rather than a generic choice.
-/

namespace Principia.MathDB.P360093

open Principia.Common.F2

/-! ## The field `𝔽₂[X]/(X⁶+X+1)` -/

/-- An element of `L`, little-endian: position `j` carries the coefficient of `α^j`. -/
abbrev Elt := Row

def zero : Elt := [false, false, false, false, false, false]

def one : Elt := [true, false, false, false, false, false]

/-- Multiplication by `α`, with the reduction `α⁶ = α + 1` folded in: the overflowing coefficient
comes back into positions `0` and `1`. -/
def shiftA (u : Elt) : Elt :=
  match u with
  | [c0, c1, c2, c3, c4, c5] =>
      if c5 then [true, !c0, c1, c2, c3, c4] else [false, c0, c1, c2, c3, c4]
  | _ => u

/-- `mulAux u v acc` adds `α^j · u` to `acc` for each `true` in `v`, shifting `u` as it goes. -/
def mulAux : Elt → Elt → Elt → Elt
  | _, [], acc => acc
  | u, b :: bs, acc => mulAux (shiftA u) bs (if b then add acc u else acc)

def mul (u v : Elt) : Elt := mulAux u v zero

/-- `u ^ n`. -/
def pow (u : Elt) : ℕ → Elt
  | 0 => one
  | n + 1 => mul (pow u n) u

/-- `α^n`. -/
def alphaPow (n : ℕ) : Elt := (List.range n).foldl (fun u _ => shiftA u) one

/-- The integer encoding the write-up displays: `Σ c_j 2^j`. -/
def enc : Elt → ℕ
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * enc bs

/-- All sixty-four elements, enumerated structurally rather than through `Nat` bit extraction. -/
def extend (l : List Elt) : List Elt := l.flatMap (fun u => [false :: u, true :: u])

def allElts : List Elt := extend (extend (extend (extend (extend (extend [[]])))))

theorem card_allElts : allElts.length = 64 := by decide

theorem allElts_nodup : allElts.dedup.length = 64 := by decide

/-- **`L` is a field.** Every nonzero element is invertible — a stronger and more directly useful
certificate than the write-up's irreducibility argument, and the only property of `X⁶+X+1` that
anything downstream uses. -/
theorem isField :
    (allElts.all fun u => u == zero || allElts.any fun v => mul u v == one) = true := by
  decide

/-- `α` generates the multiplicative group, so `L` really has degree six and `1, α, …, α⁵` is a
basis. -/
theorem alpha_order :
    (((List.range 63).map fun n => pow (alphaPow 1) (n + 1)).dedup).length = 63 := by
  decide

theorem alpha_pow_63 : pow (alphaPow 1) 63 = one := by decide

/-! ## The two subspaces -/

def Agens : List Elt := (List.range 5).map (fun j => alphaPow (j + 1))

def Bgens : List Elt := (List.range 3).map (fun j => alphaPow (j + 1))

def A : List Elt := span 6 Agens

def B : List Elt := span 6 Bgens

theorem dim_A : rank 6 Agens = 5 := by decide

theorem dim_B : rank 6 Bgens = 3 := by decide

theorem card_A : A.length = 32 := by decide

theorem card_B : B.length = 8 := by decide

/-- Both are **proper** and neither contains `1`, which is what makes the counterexample a
counterexample to the conjecture as published rather than to a degenerate reading of it. -/
theorem one_not_mem : (A.contains one) = false ∧ (B.contains one) = false := by decide

/-! ## The intermediate fields

Every intermediate degree divides `[L:K] = 6`, so the only nontrivial proper ones are two and
three, and each is the fixed set of the corresponding Frobenius power. -/

def frobIter (d : ℕ) (u : Elt) : Elt := (List.range d).foldl (fun v _ => mul v v) u

def M (d : ℕ) : List Elt := allElts.filter (fun u => frobIter d u == u)

/-- The write-up's element sets, in its own integer encoding. -/
theorem M2_enc : ((M 2).map enc) = [0, 1, 58, 59] := by decide

theorem M3_enc : ((M 3).map enc) = [0, 1, 14, 15, 22, 23, 24, 25] := by decide

theorem card_M2 : (M 2).length = 4 := by decide

theorem card_M3 : (M 3).length = 8 := by decide

/-- Each is closed under addition and multiplication, so it really is a subfield — checked, not
assumed, because an "intermediate field" that is not one would make the hypothesis vacuous. -/
theorem M2_subfield :
    ((M 2).all fun u => (M 2).all fun v => (M 2).contains (add u v) && (M 2).contains (mul u v))
      = true := by
  decide

theorem M3_subfield :
    ((M 3).all fun u => (M 3).all fun v => (M 3).contains (add u v) && (M 3).contains (mul u v))
      = true := by
  decide

/-! ## The power rows, which are what force the intersection bound on `B` -/

def Bnz : List Elt := B.filter (fun u => u ≠ zero)

theorem card_Bnz : Bnz.length = 7 := by decide

theorem cube_row_distinct : ((Bnz.map fun u => pow u 3).dedup).length = 7 := by decide

theorem seventh_row_distinct : ((Bnz.map fun u => pow u 7).dedup).length = 7 := by decide

/-- The write-up's `u³` row, as a set of encodings. -/
theorem cube_row_values :
    ((Bnz.map fun u => enc (pow u 3)).all fun n =>
      [8, 3, 59, 24, 54, 17, 15].contains n) = true := by
  decide

/-- The write-up's `u⁷` row, as a set of encodings. -/
theorem seventh_row_values :
    ((Bnz.map fun u => enc (pow u 7)).all fun n =>
      [6, 20, 26, 59, 28, 31, 1].contains n) = true := by
  decide

/-! ## The hypothesis -/

/-- `aM ∩ S`, as a list. -/
def meet (a : Elt) (Mf S : List Elt) : List Elt :=
  (Mf.map (mul a)).filter (fun u => S.contains u)

/-- `dim_K (aM ∩ S)`. -/
def dimMeet (a : Elt) (Mf S : List Elt) : ℕ := rank 6 (meet a Mf S)

theorem hyp_A_two : (allElts.all fun a => decide (dimMeet a (M 2) A ≤ 2)) = true := by decide

theorem hyp_B_two : (allElts.all fun b => decide (dimMeet b (M 2) B ≤ 1)) = true := by decide

theorem hyp_A_three : (allElts.all fun a => decide (dimMeet a (M 3) A ≤ 3)) = true := by decide

theorem hyp_B_three : (allElts.all fun b => decide (dimMeet b (M 3) B ≤ 1)) = true := by decide

/-- The hypothesis at degree two, for **every** scalar pair — recombined from the two factored
bounds rather than evaluated `64 × 64` times, because the left-hand side is a sum of independent
terms and the maximum of such a sum is the sum of the maxima. -/
theorem hyp_two (a b : Elt) (ha : a ∈ allElts) (hb : b ∈ allElts) :
    dimMeet a (M 2) A + dimMeet b (M 2) B ≤ 2 + 1 := by
  have h1 := (List.all_eq_true.mp hyp_A_two) a ha
  have h2 := (List.all_eq_true.mp hyp_B_two) b hb
  simp only [decide_eq_true_eq] at h1 h2
  omega

/-- The hypothesis at degree three, for every scalar pair. -/
theorem hyp_three (a b : Elt) (ha : a ∈ allElts) (hb : b ∈ allElts) :
    dimMeet a (M 3) A + dimMeet b (M 3) B ≤ 3 + 1 := by
  have h1 := (List.all_eq_true.mp hyp_A_three) a ha
  have h2 := (List.all_eq_true.mp hyp_B_three) b hb
  simp only [decide_eq_true_eq] at h1 h2
  omega

/-! ## The conclusion fails -/

def prodAB : List Elt := A.flatMap (fun u => B.map (mul u))

theorem dim_prodAB : rank 6 prodAB = 6 := by decide

/-- The write-up's reason: `AB` contains `α², …, α⁷`, the image of a basis under the invertible
map `u ↦ α²u`. -/
theorem alpha_sq_image :
    rank 6 ((List.range 6).map fun j => mul (alphaPow 2) (alphaPow j)) = 6 := by
  decide

/-- **Conjecture 38 is false.** `A` and `B` are proper subspaces of dimensions five and three,
neither containing `1`; the hypothesis holds at both nontrivial proper intermediate degrees for
every scalar pair; and the proposed conclusion fails by exactly one, `6 < 7`. -/
theorem conjecture_38_false :
    rank 6 Agens = 5 ∧ rank 6 Bgens = 3 ∧
      (A.contains one) = false ∧ (B.contains one) = false ∧
      (∀ a ∈ allElts, ∀ b ∈ allElts, dimMeet a (M 2) A + dimMeet b (M 2) B ≤ 2 + 1) ∧
      (∀ a ∈ allElts, ∀ b ∈ allElts, dimMeet a (M 3) A + dimMeet b (M 3) B ≤ 3 + 1) ∧
      rank 6 prodAB < rank 6 Agens + rank 6 Bgens - 1 := by
  refine ⟨dim_A, dim_B, one_not_mem.1, one_not_mem.2, ?_, ?_, ?_⟩
  · exact fun a ha b hb => hyp_two a b ha hb
  · exact fun a ha b hb => hyp_three a b ha hb
  · rw [dim_prodAB, dim_A, dim_B]
    decide

end Principia.MathDB.P360093
