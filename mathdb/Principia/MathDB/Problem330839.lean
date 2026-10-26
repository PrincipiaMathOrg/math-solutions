import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# MathDB #330839 -- Ma--Wang Conjecture 4.1 is false at `n = 7`

Write-up `mathdb-open-problems/problems/330839/solution.tex`,
*Negative real zeros in the Ma--Wang alternating-run polynomials*, 22 September 2026.
Source: S.-M. Ma and Y. Wang, published **Conjecture 4.1**.

The conjecture asserts, for every `n >= 2`, that `T_n(x)/x` has only imaginary zeros AND a
coordinate-separation property.  "Imaginary" is read as *nonreal*: the write-up records that
this is what the source intends, its statement being about conjugate pairs with nonzero real
parts.  `Conj` therefore states only the first conjunct -- no real zero -- which is the
WEAKER claim, so refuting it refutes the published conjunction a fortiori.

**No family is defined.**  `IsMaWang P` carries the source's own recurrence (their Eq. (1.1)
divided by `X`),

  `P 1 = 1`,  `P (n+1) = (1 + X + (2n-1) X^2) P n + (X - X^3) (P n)'`,

and every theorem quantifies over families satisfying it.  So `P2 ... P7` are DERIVED, and
the displayed degree-12 polynomial

  `P_7 = 1 + 63X + 1023X^2 + 4641X^3 + 16479X^4 + 26481X^5 + 37759X^6 + 26481X^7
         + 16479X^8 + 4641X^9 + 1023X^10 + 63X^11 + X^12`

is a consequence of the recurrence rather than a transcribed table.

**The refutation.**  `eval_neg_inv_twenty` reproduces the write-up's exact rational value
`P_7(-1/20) = -316770843280059/4096000000000000 < 0`, while `eval_zero` gives `P_7(0) = 1`.
The intermediate value theorem between `-1/20` and `0` then produces a real zero in
`(-1, 0)` (`exists_real_root`), and `not_conj` is the contradiction.  `eval_neg_one` records
the write-up's other endpoint value `P_7(-1) = 10395 = 11!!`, which is what gives the SECOND
real zero in `(-1, -1/20)`; one zero already refutes the conjecture, so it is not consumed.

**Not formalized, and not needed.**  The write-up strengthens the failure to *every* `n >= 7`
by an induction: if `P_n` is negative somewhere on `(-1,0)` then its minimum there is
interior, so `P_n' = 0` at that point and the recurrence gives `P_{n+1} < 0` there too.
That argument needs a compact-minimum existence step and the interior-extremum derivative
test; it strengthens the result but the refutation of Conjecture 4.1 does not rest on it,
exactly as the write-up presents it ("already fails at n = 7").

**Upstream status.**  The collaborator's own state for this problem is
`full-disproof-claim-scope-pending`; their scope audit is open.  What is certified here does
not depend on it -- the recurrence is quoted from the published source, and the refutation
is a self-contained computation plus the intermediate value theorem.

Values checked first in `Campaigns/MathDB-Formalization/verify_330839.py`.
-/

namespace Principia.MathDB.P330839

open Polynomial

/-- The Ma--Wang family `P n = T n / X`, characterised by the source's own recurrence
(their Eq. (1.1) divided by `X`).  No family is defined here, so every statement below
holds for whatever family satisfies it. -/
structure IsMaWang (P : ℕ → Polynomial ℝ) : Prop where
  one : P 1 = 1
  step : ∀ n : ℕ, 1 ≤ n →
    P (n + 1) = (1 + X + (2 * (n : Polynomial ℝ) - 1) * X ^ 2) * P n
      + (X - X ^ 3) * derivative (P n)

variable {P : ℕ → Polynomial ℝ}

theorem P2 (h : IsMaWang P) : P 2 = 1 + X + X ^ 2 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, h.step 1 (by norm_num), h.one]
  simp
  ring

theorem P3 (h : IsMaWang P) : P 3 = 1 + 3 * X + 7 * X ^ 2 + 3 * X ^ 3 + X ^ 4 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, h.step 2 (by norm_num), P2 h]
  simp
  ring

theorem P4 (h : IsMaWang P) :
    P 4 = 1 + 7 * X + 29 * X ^ 2 + 31 * X ^ 3 + 29 * X ^ 4 + 7 * X ^ 5 + X ^ 6 := by
  rw [show (4 : ℕ) = 3 + 1 from rfl, h.step 3 (by norm_num), P3 h]
  simp [map_ofNat]
  ring

theorem P5 (h : IsMaWang P) :
    P 5 = 1 + 15 * X + 101 * X ^ 2 + 195 * X ^ 3 + 321 * X ^ 4 + 195 * X ^ 5
      + 101 * X ^ 6 + 15 * X ^ 7 + X ^ 8 := by
  rw [show (5 : ℕ) = 4 + 1 from rfl, h.step 4 (by norm_num), P4 h]
  simp [map_ofNat]
  ring

theorem P6 (h : IsMaWang P) :
    P 6 = 1 + 31 * X + 327 * X ^ 2 + 1001 * X ^ 3 + 2507 * X ^ 4 + 2661 * X ^ 5
      + 2507 * X ^ 6 + 1001 * X ^ 7 + 327 * X ^ 8 + 31 * X ^ 9 + X ^ 10 := by
  rw [show (6 : ℕ) = 5 + 1 from rfl, h.step 5 (by norm_num), P5 h]
  simp [map_ofNat]
  ring

/-- The write-up's displayed `P_7`, derived from the recurrence rather than asserted. -/
theorem P7 (h : IsMaWang P) :
    P 7 = 1 + 63 * X + 1023 * X ^ 2 + 4641 * X ^ 3 + 16479 * X ^ 4 + 26481 * X ^ 5
      + 37759 * X ^ 6 + 26481 * X ^ 7 + 16479 * X ^ 8 + 4641 * X ^ 9 + 1023 * X ^ 10
      + 63 * X ^ 11 + X ^ 12 := by
  rw [show (7 : ℕ) = 6 + 1 from rfl, h.step 6 (by norm_num), P6 h]
  simp [map_ofNat]
  ring

/-! ### The witness: a real zero of `P_7` -/

theorem eval_zero (h : IsMaWang P) : (P 7).eval 0 = 1 := by
  rw [P7 h]; simp

theorem eval_neg_one (h : IsMaWang P) : (P 7).eval (-1) = 10395 := by
  rw [P7 h]; simp; norm_num

/-- The write-up's exact value, reproduced. -/
theorem eval_neg_inv_twenty (h : IsMaWang P) :
    (P 7).eval (-1 / 20) = -316770843280059 / 4096000000000000 := by
  rw [P7 h]; simp; norm_num

theorem eval_neg (h : IsMaWang P) : (P 7).eval (-1 / 20) < 0 := by
  rw [eval_neg_inv_twenty h]; norm_num

/-- **A real zero**, by the intermediate value theorem between `-1/20` and `0`. -/
theorem exists_real_root (h : IsMaWang P) :
    ∃ x : ℝ, -1 < x ∧ x < 0 ∧ (P 7).eval x = 0 := by
  have hc : ContinuousOn (fun x : ℝ => (P 7).eval x) (Set.Icc (-1 / 20 : ℝ) 0) :=
    (P 7).continuous.continuousOn
  have hmem : (0 : ℝ) ∈ Set.Ioo ((P 7).eval (-1 / 20)) ((P 7).eval 0) := by
    rw [eval_zero h]
    exact ⟨eval_neg h, by norm_num⟩
  obtain ⟨x, hx, hfx⟩ := intermediate_value_Ioo (by norm_num : (-1 / 20 : ℝ) ≤ 0) hc hmem
  exact ⟨x, by linarith [hx.1], hx.2, hfx⟩

/-- Ma--Wang Conjecture 4.1, in the WEAKEST reading the witness kills: for every `n ≥ 2`,
every zero of `T_n(x)/x` is nonreal.  The published conjecture is this conjoined with a
coordinate-separation property, so refuting this half refutes it a fortiori. -/
def Conj (P : ℕ → Polynomial ℝ) : Prop := ∀ n : ℕ, 2 ≤ n → ∀ x : ℝ, (P n).eval x ≠ 0

/-- **Conjecture 4.1 is false**, already at `n = 7`. -/
theorem not_conj (h : IsMaWang P) : ¬ Conj P := by
  intro hc
  obtain ⟨x, _, _, hx⟩ := exists_real_root h
  exact hc 7 (by norm_num) x hx

section Existence

/-! ### `IsMaWang` is SATISFIABLE — so `not_conj` refutes something

`IsMaWang` is a characterisation, and every theorem in this file is an implication from
`IsMaWang P`, `not_conj` included.  Nothing produced one, so **had the spec been unsatisfiable
`not_conj` would have been vacuously true** and "the Ma–Wang conjecture is false" would have
refuted nothing.  The spec is a plain forward recurrence, so the construction is structural.

`P 0` is left unconstrained by the source's own characterisation — the recurrence starts at
`P 1 = 1` — so `mwSeq 0` is set to `0` arbitrarily, and `isMaWang_agree` accordingly pins the
family only from index `1` on, which is exactly as much as the spec determines.
-/

/-- The Ma–Wang family, CONSTRUCTED from the source's recurrence. -/
noncomputable def mwSeq : ℕ → Polynomial ℝ
  | 0 => 0
  | 1 => 1
  | (n + 2) =>
      (1 + X + (2 * ((n + 1 : ℕ) : Polynomial ℝ) - 1) * X ^ 2) * mwSeq (n + 1)
        + (X - X ^ 3) * derivative (mwSeq (n + 1))

theorem mwSeq_one : mwSeq 1 = 1 := rfl

theorem mwSeq_step (n : ℕ) (hn : 1 ≤ n) :
    mwSeq (n + 1) = (1 + X + (2 * (n : Polynomial ℝ) - 1) * X ^ 2) * mwSeq n
      + (X - X ^ 3) * derivative (mwSeq n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rfl

/-- **The constructed family satisfies the source's recurrence.** -/
theorem isMaWang_mwSeq : IsMaWang mwSeq where
  one := mwSeq_one
  step := mwSeq_step

/-- **`IsMaWang` is satisfiable.**  Without this every theorem in this file could be vacuous. -/
theorem exists_isMaWang : ∃ P : ℕ → Polynomial ℝ, IsMaWang P := ⟨mwSeq, isMaWang_mwSeq⟩

/-- The characterisation pins the family from index `1` on — which is all it constrains. -/
theorem isMaWang_agree {P P' : ℕ → Polynomial ℝ} (h : IsMaWang P) (h' : IsMaWang P') :
    ∀ n, 1 ≤ n → P n = P' n := by
  intro n
  induction n with
  | zero => intro hn; exact absurd hn (by omega)
  | succ t ih =>
      intro _
      rcases Nat.eq_zero_or_pos t with rfl | ht
      · rw [h.one, h'.one]
      · rw [h.step t ht, h'.step t ht, ih ht]

/-- **The Ma–Wang conjecture is false, with no hypothesis at all.** -/
theorem not_conj_uncond : ¬ Conj mwSeq := not_conj isMaWang_mwSeq

end Existence

end Principia.MathDB.P330839
