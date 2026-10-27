import Mathlib

set_option autoImplicit false

/-!
# MathDB #332639 — the next-to-leading trace coefficient of a two-peg web world (SPINE)

Write-up `mathdb-open-problems/problems/332639/solution.tex` on the `mathdb-results` branch of
`antoshashakov/Principia-Math-In-Progress`.
Source: M. Dukes and C. D. White, *Web matrices: structural properties and generating
combinatorial identities*, Electron. J. Combin. **23**(1) (2016), P1.45, §7,
**Conjecture 29** (arXiv:1603.01589v1).

For the two-peg web world `W n` with `n` edges, the diagrams are indexed by permutations: the
diagram `D π` has the edge whose left endpoint is `i` ending at right endpoint `π i`. A
`k`-colouring is a surjection from the edges onto `[k]`, and *reconstruction* retains the
relative endpoint orders inside each colour class and stacks the classes in increasing colour
order. The entry `[x^k] M^(W n)_{D π, D σ}` counts the colourings of `D π` whose reconstruction
is `D σ`, so the trace counts pairs (diagram, colouring reconstructing that same diagram).
Conjecture 29 asks for

    a n = [x^(n-1)] tr M^(W n) (x),   n ≥ 2,

for which the source's Figure 7 lists `2, 8, 42, 264, 1920, 15840` and names OEIS A121635 --
with a one-place index shift in the displayed formula.

## What is proved here, and what is carried

**Carried** (`DiagCases`, one named hypothesis): the write-up's equation (2), the complete case
analysis of the *diagonal* coefficients,

    [x^(n-1)] M^(W n)_{D π, D π} = C(n,2)·(n-1)!   (π = 1)
                                 = (n-2)!          (π an adjacent transposition)
                                 = 0               (otherwise).

That is carried rather than proved because *reconstruction* is defined in Dukes–White §7 and is
not formalized in this repository, so there is no Lean object here for a proof of (2) to be
about. It enters as a hypothesis on an opaque `diag`, never as an `axiom`, so it contributes
nothing to any footprint -- and correspondingly every theorem below that depends on it says so
in its own signature.

**Proved outright**, and this is the step the write-up performs in one line:

* `card_adjTransp` -- the adjacent transpositions of `Fin (m+2)` are `m+1` *distinct*
  permutations, none of them the identity. The write-up asserts "there are `n-1` adjacent
  transpositions"; that they are pairwise distinct is what makes the summation legitimate and
  is the only place the proof could have double-counted.
* `trace_coeff` -- summing (2) over the whole symmetric group gives
  `2 · a n = (n-1)! · (n(n-1) + 2)`, i.e. `a n = (n-1)!·(C(n,2) + 1)`, which is (1).
* `trace_coeff_choose` -- the same in the write-up's own `C(n,2) + 1` shape.
* `eq_A121635` -- the index identification `a n = B (n+1)` for the A121635 formula
  `B m = (m-2)!(m² - 3m + 4)/2`, which is the *correction* the write-up contributes: the
  unshifted printed formula gives `1` at `n = 2` where the source itself gives `2`.

Everything is stated over `ℕ` and **every identity is doubled** so that no `Nat` division
occurs, and every argument is written in the shifted variable `n = m + 2` so that no `Nat`
subtraction occurs either. `B` is likewise given a subtraction-free definition and the
agreement with the printed formula is recorded in `twoB_eq_printed` rather than assumed.

No claim is made about Problem 25 of the source (the general enumeration) or about the
polyomino side of A121635, which the write-up also disclaims.
-/

namespace Principia.MathDB.P332639

open Finset

/-! ### The adjacent transpositions

`adjTransp j` swaps the two neighbouring points `j` and `j+1` of `Fin (m+2)`. The write-up's
"there are `n-1` adjacent transpositions, none of them the identity" is the content of
`adjTransp_ne_one` and `adjTransp_injective`. -/

/-- The transposition of the neighbouring points `j.castSucc` and `j.succ` of `Fin (m+2)`. -/
def adjTransp {m : ℕ} (j : Fin (m + 1)) : Equiv.Perm (Fin (m + 2)) :=
  Equiv.swap j.castSucc j.succ

theorem castSucc_ne_succ {m : ℕ} (j : Fin (m + 1)) : j.castSucc ≠ j.succ := by
  -- `Fin.castSucc_lt_succ` takes its index IMPLICITLY; applying it to `j` is a type error.
  have h : j.castSucc < j.succ := Fin.castSucc_lt_succ
  exact ne_of_lt h

theorem adjTransp_apply_castSucc {m : ℕ} (j : Fin (m + 1)) :
    adjTransp j j.castSucc = j.succ := Equiv.swap_apply_left _ _

theorem adjTransp_apply_succ {m : ℕ} (j : Fin (m + 1)) :
    adjTransp j j.succ = j.castSucc := Equiv.swap_apply_right _ _

theorem adjTransp_ne_one {m : ℕ} (j : Fin (m + 1)) : adjTransp j ≠ 1 := by
  intro h
  have h0 : adjTransp j j.castSucc = j.castSucc := by rw [h]; simp
  rw [adjTransp_apply_castSucc] at h0
  exact castSucc_ne_succ j h0.symm

/-- Distinct `j` give distinct transpositions. This is the step that makes the summation in
`trace_coeff` legitimate: the write-up counts `n-1` adjacent transpositions, and if two of them
coincided the count would be wrong. Proved from the support: `support (swap a b) = {a, b}` for
`a ≠ b`, so equal permutations give equal two-element supports, and the `castSucc < succ`
ordering picks the same element out of each. -/
theorem adjTransp_injective {m : ℕ} : Function.Injective (adjTransp (m := m)) := by
  intro j k h
  -- Apply both permutations to `j.castSucc`, which `adjTransp j` sends to `j.succ`.
  have hk : adjTransp k j.castSucc = j.succ := by
    rw [← h]; exact adjTransp_apply_castSucc j
  rw [adjTransp, Equiv.swap_apply_def] at hk
  by_cases h1 : j.castSucc = k.castSucc
  · exact Fin.castSucc_injective _ h1
  · by_cases h2 : j.castSucc = k.succ
    · -- then `hk` says `k.castSucc = j.succ`, so each index is the other's successor
      rw [if_neg h1, if_pos h2] at hk
      exfalso
      have v2 : (j : ℕ) = (k : ℕ) + 1 := by
        have := congrArg Fin.val h2
        simpa using this
      have v3 : (k : ℕ) = (j : ℕ) + 1 := by
        have := congrArg Fin.val hk
        simpa using this
      omega
    · rw [if_neg h1, if_neg h2] at hk
      exact absurd hk (castSucc_ne_succ j)

/-- The `m+1` adjacent transpositions, as a `Finset` of permutations. -/
def adjSet (m : ℕ) : Finset (Equiv.Perm (Fin (m + 2))) :=
  Finset.univ.image (adjTransp (m := m))

theorem card_adjTransp (m : ℕ) : (adjSet m).card = m + 1 := by
  rw [adjSet, Finset.card_image_of_injective _ adjTransp_injective, Finset.card_univ,
    Fintype.card_fin]

theorem one_notMem_adjSet (m : ℕ) : (1 : Equiv.Perm (Fin (m + 2))) ∉ adjSet m := by
  simp only [adjSet, Finset.mem_image, Finset.mem_univ, true_and, not_exists]
  intro j hj
  exact adjTransp_ne_one j hj

/-! ### The carried case analysis

`diag n π` is the next-to-leading diagonal coefficient `[x^(n-1)] M^(W n)_{D π, D π}`. It is a
PARAMETER, and `DiagCases` is the write-up's equation (2) about it. -/

/-- The write-up's equation (2): the complete case analysis of the diagonal coefficients of the
web matrix at the next-to-leading power. NOT proved here -- reconstruction is defined in
Dukes–White §7 and is not formalized in this repository. -/
structure DiagCases (diag : ∀ n : ℕ, Equiv.Perm (Fin n) → ℕ) : Prop where
  /-- At the identity diagram every surjective `(n-1)`-colouring reconstructs the identity:
  `C(n,2)` choices of the two-edge class, then `(n-1)!` bijections onto the colours. -/
  id_case : ∀ m : ℕ, diag (m + 2) 1 = (m + 2).choose 2 * (m + 1).factorial
  /-- At an adjacent transposition the two-edge class is forced, its colour is forced, and the
  remaining `n-2` edges take the remaining colours in any order. -/
  swap_case : ∀ (m : ℕ) (j : Fin (m + 1)), diag (m + 2) (adjTransp j) = m.factorial
  /-- No other diagram is its own reconstruction. -/
  other : ∀ (m : ℕ) (π : Equiv.Perm (Fin (m + 2))),
    π ≠ 1 → π ∉ adjSet m → diag (m + 2) π = 0

/-- The trace at the next-to-leading power: `a n = ∑_π [x^(n-1)] M_{D π, D π}`. -/
def traceCoeff (diag : ∀ n : ℕ, Equiv.Perm (Fin n) → ℕ) (n : ℕ) : ℕ :=
  ∑ π : Equiv.Perm (Fin n), diag n π

/-! ### The arithmetic core, proved outright

These two lemmas are about `ℕ` alone and carry nothing. -/

/-- `2·C(m+2,2) = (m+2)(m+1)`: the write-up's binomial, cleared of division. -/
theorem two_mul_choose_two (m : ℕ) : 2 * (m + 2).choose 2 = (m + 2) * (m + 1) := by
  induction m with
  | zero => decide
  | succ k ih =>
    have hsucc : (k + 1 + 2).choose 2 = (k + 2).choose 1 + (k + 2).choose 2 :=
      Nat.choose_succ_succ (k + 2) 1
    have hone : (k + 2).choose 1 = k + 2 := Nat.choose_one_right _
    calc 2 * (k + 1 + 2).choose 2
        = 2 * ((k + 2) + (k + 2).choose 2) := by rw [hsucc, hone]
      _ = 2 * (k + 2) + 2 * (k + 2).choose 2 := by ring
      _ = 2 * (k + 2) + (k + 2) * (k + 1) := by rw [ih]
      _ = (k + 1 + 2) * (k + 1 + 1) := by ring

/-- The write-up's one-line summation, cleared of division and of `Nat` subtraction. -/
theorem sum_cases (m : ℕ) :
    2 * ((m + 2).choose 2 * (m + 1).factorial + (m + 1) * m.factorial)
      = (m + 1).factorial * ((m + 2) * (m + 1) + 2) := by
  have hfac : (m + 1) * m.factorial = (m + 1).factorial := (Nat.factorial_succ m).symm
  have hch : 2 * (m + 2).choose 2 = (m + 2) * (m + 1) := two_mul_choose_two m
  calc 2 * ((m + 2).choose 2 * (m + 1).factorial + (m + 1) * m.factorial)
      = (2 * (m + 2).choose 2) * (m + 1).factorial + 2 * ((m + 1) * m.factorial) := by ring
    _ = ((m + 2) * (m + 1)) * (m + 1).factorial + 2 * (m + 1).factorial := by
          rw [hch, hfac]
    _ = (m + 1).factorial * ((m + 2) * (m + 1) + 2) := by ring

/-! ### The theorem

Both statements below carry `DiagCases` in their signature; neither is unconditional. -/

/-- **MathDB #332639, equation (1)**, in the doubled, subtraction-free form:
`2·a n = (n-1)!·(n(n-1) + 2)` at `n = m+2`. -/
theorem trace_coeff {diag : ∀ n : ℕ, Equiv.Perm (Fin n) → ℕ} (hd : DiagCases diag) (m : ℕ) :
    2 * traceCoeff diag (m + 2) = (m + 1).factorial * ((m + 2) * (m + 1) + 2) := by
  classical
  have hsplit :
      ∑ π ∈ insert (1 : Equiv.Perm (Fin (m + 2))) (adjSet m), diag (m + 2) π
        = ∑ π : Equiv.Perm (Fin (m + 2)), diag (m + 2) π := by
    refine Finset.sum_subset (Finset.subset_univ _) ?_
    intro π _ hπ
    have h1 : π ≠ 1 := by
      intro h; exact hπ (by rw [h]; exact Finset.mem_insert_self _ _)
    have h2 : π ∉ adjSet m := fun h => hπ (Finset.mem_insert_of_mem h)
    exact hd.other m π h1 h2
  have hins : ∑ π ∈ insert (1 : Equiv.Perm (Fin (m + 2))) (adjSet m), diag (m + 2) π
      = diag (m + 2) 1 + ∑ π ∈ adjSet m, diag (m + 2) π :=
    Finset.sum_insert (one_notMem_adjSet m)
  have himg : ∑ π ∈ adjSet m, diag (m + 2) π
      = ∑ j : Fin (m + 1), diag (m + 2) (adjTransp j) := by
    rw [adjSet, Finset.sum_image (fun a _ b _ hab => adjTransp_injective hab)]
  have hswap : ∑ j : Fin (m + 1), diag (m + 2) (adjTransp j) = (m + 1) * m.factorial := by
    rw [Finset.sum_congr rfl (fun j _ => hd.swap_case m j), Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have : traceCoeff diag (m + 2)
      = (m + 2).choose 2 * (m + 1).factorial + (m + 1) * m.factorial := by
    rw [traceCoeff, ← hsplit, hins, himg, hswap, hd.id_case m]
  rw [this]
  exact sum_cases m

/-- **MathDB #332639, equation (1)** in the write-up's own `(n-1)!·(C(n,2)+1)` shape. -/
theorem trace_coeff_choose {diag : ∀ n : ℕ, Equiv.Perm (Fin n) → ℕ} (hd : DiagCases diag)
    (m : ℕ) :
    traceCoeff diag (m + 2) = (m + 1).factorial * ((m + 2).choose 2 + 1) := by
  have h2 : 2 * traceCoeff diag (m + 2) = (m + 1).factorial * ((m + 2) * (m + 1) + 2) :=
    trace_coeff hd m
  have hch : 2 * (m + 2).choose 2 = (m + 2) * (m + 1) := two_mul_choose_two m
  have h3 : 2 * ((m + 1).factorial * ((m + 2).choose 2 + 1))
      = (m + 1).factorial * ((m + 2) * (m + 1) + 2) := by
    calc 2 * ((m + 1).factorial * ((m + 2).choose 2 + 1))
        = (m + 1).factorial * (2 * (m + 2).choose 2 + 2) := by ring
      _ = (m + 1).factorial * ((m + 2) * (m + 1) + 2) := by rw [hch]
  -- `omega` cannot cancel the `2` here: every term is a product, which it treats as opaque.
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) (h2.trans h3.symm)

/-! ### The index identification with OEIS A121635

The recorded formula is `B m = (m-2)!·(m² - 3m + 4)/2` for `m ≥ 2`. Written at `m = k + 3` it is
subtraction- and division-free, and `twoB_eq_printed` records that this is the same number as
the printed expression rather than leaving the reader to check it. -/

/-- `2·B (k+3)`, where `B` is the A121635 formula. Subtraction- and division-free by
construction. -/
def twoB (k : ℕ) : ℕ := (k + 1).factorial * (k * k + 3 * k + 4)

/-- `twoB` really is twice the printed formula `(m-2)!(m² - 3m + 4)/2` at `m = k+3`: the
printed numerator equals `k² + 3k + 4` there. -/
theorem twoB_eq_printed (k : ℕ) :
    twoB k = ((k + 3) - 2).factorial * ((k + 3) * (k + 3) + 4 - 3 * (k + 3)) := by
  have h1 : (k + 3) - 2 = k + 1 := by omega
  -- `Nat` subtraction, discharged by exhibiting the addition it inverts rather than by `omega`,
  -- which cannot see through `k * k`.
  have h2 : (k + 3) * (k + 3) + 4 - 3 * (k + 3) = k * k + 3 * k + 4 :=
    Nat.sub_eq_of_eq_add (by ring)
  rw [twoB, h1, h2]

/-- **The index correction.** `a n = B (n+1)`: with `n = m+2` the trace coefficient equals the
A121635 value at `m+3`, not at `m+2`. This is what the write-up contributes beyond the
enumeration -- the source's printed formula, read at the source's own index, gives `1` at
`n = 2` where the source's own figure gives `2`. -/
theorem eq_A121635 {diag : ∀ n : ℕ, Equiv.Perm (Fin n) → ℕ} (hd : DiagCases diag) (m : ℕ) :
    2 * traceCoeff diag (m + 2) = twoB m := by
  rw [trace_coeff hd m, twoB]
  congr 1
  ring

/-! ### The six values the source's Figure 7 lists

`2, 8, 42, 264, 1920, 15840` at `n = 2, …, 7`. These are a check on the FORMULA, not on the
hypothesis: they are computed from `(m+1)!·(C(m+2,2)+1)`, so they confirm that the closed form
reproduces the source's figure, and they would still hold if (2) were false. -/

theorem value_n2 : (0 + 1).factorial * ((0 + 2).choose 2 + 1) = 2 := by decide
theorem value_n3 : (1 + 1).factorial * ((1 + 2).choose 2 + 1) = 8 := by decide
theorem value_n4 : (2 + 1).factorial * ((2 + 2).choose 2 + 1) = 42 := by decide
theorem value_n5 : (3 + 1).factorial * ((3 + 2).choose 2 + 1) = 264 := by decide
theorem value_n6 : (4 + 1).factorial * ((4 + 2).choose 2 + 1) = 1920 := by decide
theorem value_n7 : (5 + 1).factorial * ((5 + 2).choose 2 + 1) = 15840 := by decide

end Principia.MathDB.P332639
