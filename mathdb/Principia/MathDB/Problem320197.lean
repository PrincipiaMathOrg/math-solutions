import Mathlib.Data.List.Basic
import Mathlib.Data.List.Range
import Mathlib.Tactic.NormNum

/-!
# MathDB #320197 — Pan's Conjecture 6 on Langford coverage sequences is FALSE

Write-up: `antoshashakov/Principia-Math-In-Progress`, `mathdb-open-problems/problems/320197/`
(`solution.tex`), refuting Conjecture 6 of Z. Pan, *The Multiple Permutation Problem and Some
Conjectures*, arXiv:1007.4663v1, p. 4.

**The objects.**  A solution to `(2, n)` — a *Langford word* — is a word of length `2n` containing
two copies of every `k ∈ {1, …, n}` with exactly `k` entries between the copies, so if `θ k` is the
first occurrence then the second is at `θ k + k + 1`.  Its **coverage sequence** counts inclusive
interval coverage,

  `μ i = #{k ∈ {1, …, n} : θ k ≤ i ≤ θ k + k + 1}`,  `1 ≤ i ≤ 2n`,

which is the reading consistent with the source's own identity `∑ᵢ μ i = (n² + 5n)/2`.  Conjecture 6
asserts that `μ` is weakly unimodal, with its mode at some `i ≤ n` where `μ i = ⌊(n + 3)/2⌋`.

**What is refuted, and why it is stated weakly.**  `PanConj6` below keeps only the **unimodality**
clause and drops the mode's location and value.  That is deliberate: refuting a *weaker* statement
is the stronger result, and the witness kills unimodality outright — no mode exists anywhere — so
nothing is gained by encoding the parts that would make the conjecture easier to break.  The value
claim fails too, and is recorded separately by `maxCover_witness` rather than folded in.

**The witness** is the `n = 7` word `W = (7,3,1,6,1,3,4,5,7,2,6,4,2,5)`, whose coverage sequence is
`(1,2,3,4,4,3,3,4,4,4,4,3,2,1)`: it falls from `μ₅ = 4` to `μ₆ = 3` and rises again to `μ₈ = 4`, and
its maximum is `4` against the conjectured `⌊(7 + 3)/2⌋ = 5`.

Everything here is a finite computation on concrete lists, so the gate is the whole audit — every
declaration below is closed by `decide` and its axiom footprint is the empty set or `propext`.
-/

namespace Principia.MathDB.P320197

/-- The 1-based positions at which `k` occurs in `S`. -/
def occs (S : List ℕ) (k : ℕ) : List ℕ :=
  (List.range S.length).filterMap (fun i => if S.getD i 0 = k then some (i + 1) else none)

/-- `S` is a Langford word for `(2, n)`: length `2n`, letters in `{1, …, n}`, and every `k` occurs
exactly twice with exactly `k` entries between the two copies. -/
def isLangfordB (n : ℕ) (S : List ℕ) : Bool :=
  decide (S.length = 2 * n) &&
    S.all (fun a => decide (1 ≤ a) && decide (a ≤ n)) &&
    (List.range' 1 n).all (fun k =>
      (occs S k).length == 2 && decide ((occs S k).headD 0 + k + 1 = (occs S k).getD 1 0))

/-- The coverage sequence `(μ 1, …, μ (2n))`.  The first occurrences are computed once per letter
rather than once per `(i, k)` pair, which is what keeps `decide` cheap. -/
def coverSeq (n : ℕ) (S : List ℕ) : List ℕ :=
  let T := (List.range' 1 n).map (fun k => ((occs S k).headD 0, k))
  (List.range' 1 (2 * n)).map (fun i =>
    (T.filter (fun q => decide (q.1 ≤ i) && decide (i ≤ q.1 + q.2 + 1))).length)

/-- Weak unimodality: some index `m` has the entries weakly increasing up to `m` and weakly
decreasing after it. -/
def UnimodalB (L : List ℕ) : Bool :=
  (List.range L.length).any (fun m =>
    (List.range (L.length - 1)).all (fun i =>
      if i + 1 ≤ m then decide (L.getD i 0 ≤ L.getD (i + 1) 0)
      else decide (L.getD (i + 1) 0 ≤ L.getD i 0)))

/-- Pan's Conjecture 6, unimodality clause only — the weakest reading, so that refuting it refutes
every stronger one. -/
def PanConj6 : Prop :=
  ∀ (n : ℕ) (S : List ℕ), isLangfordB n S = true → UnimodalB (coverSeq n S) = true

/-- The counterexample word. -/
def W : List ℕ := [7, 3, 1, 6, 1, 3, 4, 5, 7, 2, 6, 4, 2, 5]

/-- `W` really is a Langford word for `(2, 7)`.  This is the hypothesis of the conjecture, and it is
the half a counterexample most often gets wrong. -/
theorem W_isLangford : isLangfordB 7 W = true := by decide

/-- The first occurrences, matching the source's table `θ = (3, 10, 2, 7, 8, 4, 1)`. -/
theorem W_thetas : ((List.range' 1 7).map (fun k => (occs W k).headD 0)) = [3, 10, 2, 7, 8, 4, 1] :=
  by decide

/-- The coverage sequence, matching equation (2) of the write-up. -/
theorem W_coverSeq : coverSeq 7 W = [1, 2, 3, 4, 4, 3, 3, 4, 4, 4, 4, 3, 2, 1] := by decide

/-- The source's total-weight identity `∑ᵢ μ i = (n² + 5n)/2` survives at `n = 7`: `42`.  Recorded
because it is what pins this reading of the definition. -/
theorem W_coverSum : (coverSeq 7 W).sum = (7 * 7 + 5 * 7) / 2 := by decide

/-- **The coverage sequence is not weakly unimodal.**  It falls `μ₅ = 4 → μ₆ = 3` and rises again to
`μ₈ = 4`, so no mode exists at any index. -/
theorem W_not_unimodal : UnimodalB (coverSeq 7 W) = false := by decide

/-- The maximum is `4`, against the conjectured `⌊(7 + 3)/2⌋ = 5`.  An independent failure of the
conjecture, kept separate from the unimodality clause. -/
theorem maxCover_witness : (coverSeq 7 W).foldr max 0 = 4 ∧ (7 + 3) / 2 = 5 := by decide

/-- **MathDB #320197: Pan's Conjecture 6 is false.** -/
theorem not_panConj6 : ¬ PanConj6 := by
  intro h
  have := h 7 W W_isLangford
  rw [W_not_unimodal] at this
  exact Bool.false_ne_true this

end Principia.MathDB.P320197
