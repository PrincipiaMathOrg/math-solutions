import Mathlib

/-!
# MathDB #347624 — the parabola lower bound for the inverse question-mark function is FALSE

Write-up `mathdb-open-problems/problems/347624/solution.tex`,
*A counterexample in every band of the parabola conjecture*, 18 September 2026.

Vielhaber's Conjecture 22 asserts that the inverse binary question-mark function `φ` satisfies,
for every `k ≥ 0` and every `y ∈ [2^{-k-1}, 2^{-k}]`,

`φ y ≥ Q_k y`,  `Q_k y = (4/3)·2^k·(y − (3/4)·2^{-k})² + y − (1/12)·2^{-k}`.

At `k = 0` and `y = 7/8` this fails: `φ (7/8) = 4/5` while `Q₀ (7/8) = 13/16`, short by exactly
`1/80`.  The point is interior to the band and distinct from the three points where the source
specifies equality (the two endpoints and the three-quarter point `3/4`).

## How `φ (7/8) = 4/5` is established, rather than assumed

The source defines `φ` through a coding of even-length continued fractions.  For
`b = 2^ℓ + ∑_{j<ℓ} a_j 2^j`,

`C_I b = 0^ℓ 1 ā_{ℓ-1} ⋯ ā_0`,  `C_II b = 1^ℓ 0 a_{ℓ-1} ⋯ a_0`,

and a fraction `[b₁,…,b_{2m}]` — in the convention `[b₁,b₂] = 1/(b₁ + 1/b₂)` — maps to the word
`C_I b₁ · C_II b₂ ⋯`, whose binary value is `y`, with `φ y` the fraction.  Both codings are
defined here **in general**, from `Nat.size` and `Nat.testBit`, not tabulated for the witness:
`codeword [1,4] = 111000`, so `y = (0.111000)₂ = 7/8`, and `cfVal [1,4] = 4/5`.

## Scope

This refutes the **inequality** of Conjecture 22.  It says nothing about the equality claims at
the band endpoints and the three-quarter point, which the source states separately and which this
witness does not touch — the chosen `y` is deliberately none of them.

Checked in Python before formalizing: `C_I 1 = 1`, `C_II 4 = 11000`, the concatenation, the binary
value `7/8`, the continued fraction `4/5`, `Q₀ (7/8) = 13/16`, and the deficit `1/80`.
-/

namespace Principia.MathDB.P347624

/-- `ℓ` in `b = 2^ℓ + ∑_{j<ℓ} a_j 2^j`: the index of the leading binary digit. -/
def hiBit (b : ℕ) : ℕ := Nat.size b - 1

/-- `C_I b = 0^ℓ 1 ā_{ℓ-1} ⋯ ā_0`. -/
def codeI (b : ℕ) : List Bool :=
  List.replicate (hiBit b) false ++
    true :: ((List.range (hiBit b)).reverse.map fun j => !(b.testBit j))

/-- `C_II b = 1^ℓ 0 a_{ℓ-1} ⋯ a_0`. -/
def codeII (b : ℕ) : List Bool :=
  List.replicate (hiBit b) true ++
    false :: ((List.range (hiBit b)).reverse.map fun j => b.testBit j)

/-- The codings agree with the write-up on the witness. -/
theorem codeI_one : codeI 1 = [true] := by decide

theorem codeII_four : codeII 4 = [true, true, false, false, false] := by decide

/-- `C_I b₁ · C_II b₂ ⋯`, alternating as the source prescribes. -/
def codeword : List ℕ → List Bool
  | [] => []
  | [b] => codeI b
  | b₁ :: b₂ :: rest => codeI b₁ ++ codeII b₂ ++ codeword rest

/-- The binary fraction `(0.w)₂`. -/
def binVal : List Bool → ℚ
  | [] => 0
  | b :: t => (if b then 1 / 2 else 0) + binVal t / 2

/-- `[b₁,…,b_n] = 1/(b₁ + 1/(b₂ + ⋯))`, the source's convention. -/
def cfVal : List ℕ → ℚ
  | [] => 0
  | b :: t => 1 / ((b : ℚ) + cfVal t)

/-- The conjectured lower bound at `k = 0`. -/
def Q0 (y : ℚ) : ℚ := (4 / 3) * (y - 3 / 4) ^ 2 + y - 1 / 12

/-- The witness word is `111000`. -/
theorem codeword_witness : codeword [1, 4] = [true, true, true, false, false, false] := by
  decide

/-- Its binary value is `7/8`, so this is the address of `y = 7/8`. -/
theorem y_witness : binVal (codeword [1, 4]) = 7 / 8 := by
  rw [codeword_witness]
  norm_num [binVal]

/-- The continued fraction it codes is `4/5`, i.e. `φ (7/8) = 4/5`. -/
theorem phi_witness : cfVal [1, 4] = 4 / 5 := by
  norm_num [cfVal]

/-- The conjectured bound at the witness is `13/16`. -/
theorem Q0_witness : Q0 (7 / 8) = 13 / 16 := by
  norm_num [Q0]

/-- `7/8` lies in the `k = 0` band and is none of the three points where the source asserts
equality (`1/2`, `1`, and the three-quarter point `3/4`). -/
theorem y_interior : (1 / 2 : ℚ) ≤ 7 / 8 ∧ (7 / 8 : ℚ) ≤ 1 ∧
    (7 / 8 : ℚ) ≠ 1 / 2 ∧ (7 / 8 : ℚ) ≠ 1 ∧ (7 / 8 : ℚ) ≠ 3 / 4 := by
  norm_num

/-- **MathDB #347624 — Conjecture 22 is FALSE.**  At `y = 7/8`, an interior point of the `k = 0`
band distinct from all three specified equality points, the address codes `φ (7/8) = 4/5` while
the conjectured bound is `13/16`, short by `1/80`. -/
theorem main :
    binVal (codeword [1, 4]) = 7 / 8 ∧ cfVal [1, 4] = 4 / 5 ∧
      Q0 (7 / 8) = 13 / 16 ∧ cfVal [1, 4] < Q0 (7 / 8) ∧
      Q0 (7 / 8) - cfVal [1, 4] = 1 / 80 := by
  refine ⟨y_witness, phi_witness, Q0_witness, ?_, ?_⟩
  · rw [phi_witness, Q0_witness]; norm_num
  · rw [phi_witness, Q0_witness]; norm_num

end Principia.MathDB.P347624
