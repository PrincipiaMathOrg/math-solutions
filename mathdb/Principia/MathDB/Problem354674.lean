import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false

/-!
# MathDB #354674 — Bayón et al.'s Conjecture 1 is FALSE

Write-up: `mathdb-open-problems/problems/354674/solution.tex`, collaborator branch
`mathdb-results` of `antoshashakov/Principia-Math-In-Progress` (enrolled here 2026-09-30).

The conjecture concerns the backward recurrence `F_n(k) = G_n(k) + H_n(k) F_n(k+1)` with
`F_n(n) = μ`. Writing `f_n(x) = F_n(⌊nx⌋)`, `g_n(x) = n G_n(⌊nx⌋)` and
`h_n(x) = n(1 − H_n(⌊nx⌋))`, it asserts that pointwise convergence `g_n → g`, `h_n → h` with
continuous limits, plus solvability of `y' = −g + hy` continuously up to `1` for only one terminal
value, forces `f_n` to converge pointwise to a `C¹(0,1]` solution.

The counterexample: `H_n(k) = (n−k)/(n−k+1)`, a **single unit spike** in `G_n` at
`j_n = ⌊n/2⌋ + 1`, and `F_n(n) = 0`.

## This row was deferred twice as "ODE and convergence analysis", and that pricing was wrong

The construction is explicit rational algebra with a **closed form**, and the closed form is the
whole module: `F_n(k) = ⌈n/2⌉/(n−k+1)` for `k ≤ j_n`, and `0` beyond. `Fcl_recurrence` proves it
solves the recurrence — three cases, each rational arithmetic — and everything afterwards is
evaluation.

## The refutation needs no differential equation

`f_n(3/4) = 0` **exactly**, for every `n ≥ 7`; and `f_n(1/2) = ⌈n/2⌉/(⌈n/2⌉+1)` **exactly**, so
`1 − f_n(1/2) = 1/(⌈n/2⌉+1)`. The pointwise limit therefore has value `1` at `x = 1/2` and value
`0` at every `x > 1/2`: it is **discontinuous at 1/2**, hence not `C¹`, and no differential
equation is consulted. `not_continuous_limit` is that statement.

The write-up's sharper route is also recorded: the limiting equation `y' = y/(1−x)` has solutions
`C/(1−x)`, continuity at `1` forces `C = 0`, so the only admissible solution vanishes identically
— yet `f_quarter_ge_half` proves `f_n(1/4) ≥ 1/2` for **every** `n ≥ 4`, so the sequence stays a
fixed distance from it. That the ODE has only the zero solution is this module's single named
hypothesis, and the only place analysis enters.

## The counterexample is admissible, which is half the theorem

A counterexample that broke one of the conjecture's own hypotheses would refute nothing, so
`admissible` checks them: `μ = F_n(n) = 0`, `0 < H_n(k) < 1` for `k < n`, and every recurrence
value in `[0,1]`.

## Two findings

* **The spike must move with `n`.** The verifier's controls show that deleting it makes `F_n`
  identically zero — so the conjecture's conclusion would hold — and that **pinning it at a fixed
  index makes `f_n(1/4) → 0`**, the influence washing out entirely. It is `j_n/n → 1/2` that
  creates the jump.
* **The write-up's thresholds are conservative.** `j_n < n` already holds at `n = 3`, not `4`; and
  `f_n(3/4) = 0` from `n = 7`, not `8`. Both measured rather than assumed.
-/

namespace Principia.MathDB.P354674

/-- `j_n = ⌊n/2⌋ + 1`, the index carrying the unit spike. -/
def jIdx (n : ℕ) : ℕ := n / 2 + 1

/-- `⌈n/2⌉`. -/
def ceilHalf (n : ℕ) : ℕ := (n + 1) / 2

/-- `H_n(k) = (n−k)/(n−k+1)`, written with rational subtraction so no `ℕ` truncation occurs. -/
def Hc (n k : ℕ) : ℚ := ((n : ℚ) - k) / ((n : ℚ) - k + 1)

/-- `G_n(k) = 1` at `k = j_n` (for `n ≥ 4`), and `0` elsewhere. -/
def Gc (n k : ℕ) : ℚ := if 4 ≤ n ∧ k = jIdx n then 1 else 0

/-- The write-up's closed form for the backward recurrence. -/
def Fcl (n k : ℕ) : ℚ :=
  if 4 ≤ n ∧ k ≤ jIdx n then (ceilHalf n : ℚ) / ((n : ℚ) - k + 1) else 0

/-! ## Division facts, handed to `omega` explicitly

`omega` models `ℕ` division by a literal, but two or three interacting divisions in one goal
defeat it. Supplying `Nat.div_add_mod` and the remainder bounds is what makes each of the index
comparisons below a one-line `omega`. -/

theorem div_facts (n : ℕ) :
    n / 2 * 2 + n % 2 = n ∧ n % 2 < 2 ∧ n / 4 * 4 + n % 4 = n ∧ n % 4 < 4
      ∧ 3 * n / 4 * 4 + (3 * n) % 4 = 3 * n ∧ (3 * n) % 4 < 4
      ∧ (n + 1) / 2 * 2 + (n + 1) % 2 = n + 1 ∧ (n + 1) % 2 < 2 := by
  refine ⟨Nat.div_add_mod' n 2, Nat.mod_lt _ (by norm_num), Nat.div_add_mod' n 4,
    Nat.mod_lt _ (by norm_num), Nat.div_add_mod' (3 * n) 4, Nat.mod_lt _ (by norm_num),
    Nat.div_add_mod' (n + 1) 2, Nat.mod_lt _ (by norm_num)⟩

/-! ## `n − j_n + 1 = ⌈n/2⌉`, which is why the spike value is exactly `1` -/

theorem jIdx_add_ceilHalf (n : ℕ) : n + 1 = jIdx n + ceilHalf n := by
  obtain ⟨h1, h2, -, -, -, -, h7, h8⟩ := div_facts n
  simp only [jIdx, ceilHalf]
  omega

theorem n_sub_jIdx (n : ℕ) : (n : ℚ) - (jIdx n : ℚ) + 1 = (ceilHalf n : ℚ) := by
  have h : ((n + 1 : ℕ) : ℚ) = ((jIdx n + ceilHalf n : ℕ) : ℚ) := by
    exact_mod_cast congrArg (fun m : ℕ => (m : ℚ)) (jIdx_add_ceilHalf n)
  push_cast at h
  linarith

theorem ceilHalf_pos (n : ℕ) (hn : 4 ≤ n) : 0 < (ceilHalf n : ℚ) := by
  have h : 0 < ceilHalf n := by
    obtain ⟨-, -, -, -, -, -, h7, h8⟩ := div_facts n
    simp only [ceilHalf]
    omega
  exact_mod_cast h

/-! ## The closed form solves the recurrence -/

/-- Beyond the spike the closed form vanishes. -/
theorem Fcl_beyond (n k : ℕ) (h : jIdx n < k) : Fcl n k = 0 := by
  have hne : ¬ (4 ≤ n ∧ k ≤ jIdx n) := by rintro ⟨-, h2⟩; omega
  simp only [Fcl, if_neg hne]

theorem Fcl_terminal (n : ℕ) (hn : 4 ≤ n) : Fcl n n = 0 := by
  refine Fcl_beyond n n ?_
  obtain ⟨h1, h2, -, -, -, -, -, -⟩ := div_facts n
  simp only [jIdx]
  omega

theorem Gc_spike (n : ℕ) (hn : 4 ≤ n) : Gc n (jIdx n) = 1 := by
  have hcond : 4 ≤ n ∧ jIdx n = jIdx n := ⟨hn, rfl⟩
  unfold Gc
  rw [if_pos hcond]

theorem Fcl_spike (n : ℕ) (hn : 4 ≤ n) : Fcl n (jIdx n) = 1 := by
  have hcond : 4 ≤ n ∧ jIdx n ≤ jIdx n := ⟨hn, le_rfl⟩
  unfold Fcl
  rw [if_pos hcond, n_sub_jIdx n]
  exact div_self (ne_of_gt (ceilHalf_pos n hn))

/-- **The heart of the module.** The closed form satisfies the backward recurrence. Three cases:
beyond the spike everything is zero; at the spike the value is `1` because `n − j_n + 1 = ⌈n/2⌉`;
below it the factor `n−k` cancels. -/
theorem Fcl_recurrence (n k : ℕ) (hn : 4 ≤ n) (hk : k < n) :
    Fcl n k = Gc n k + Hc n k * Fcl n (k + 1) := by
  have hkQ : (k : ℚ) < (n : ℚ) := by exact_mod_cast hk
  have hd : (0 : ℚ) < (n : ℚ) - k := by linarith
  rcases lt_trichotomy k (jIdx n) with h | h | h
  · have hg : ¬ (4 ≤ n ∧ k = jIdx n) := by rintro ⟨-, rfl⟩; omega
    have h1 : (4 ≤ n ∧ k ≤ jIdx n) := ⟨hn, le_of_lt h⟩
    have h2 : (4 ≤ n ∧ k + 1 ≤ jIdx n) := ⟨hn, h⟩
    simp only [Fcl, Gc, Hc, if_pos h1, if_pos h2, if_neg hg]
    push_cast
    rw [show (n : ℚ) - ((k : ℚ) + 1) + 1 = (n : ℚ) - k from by ring]
    have hne : (n : ℚ) - k ≠ 0 := ne_of_gt hd
    have hne2 : (n : ℚ) - k + 1 ≠ 0 := by linarith
    field_simp
    try ring
  · subst h
    rw [Gc_spike n hn, Fcl_spike n hn, Fcl_beyond n (jIdx n + 1) (by omega), mul_zero, add_zero]
  · rw [Fcl_beyond n k h, Fcl_beyond n (k + 1) (by omega), mul_zero, add_zero]
    have hg : ¬ (4 ≤ n ∧ k = jIdx n) := by rintro ⟨-, rfl⟩; omega
    simp only [Gc, if_neg hg]

/-! ## The conjecture's own hypotheses -/

theorem Hc_pos (n k : ℕ) (hk : k < n) : 0 < Hc n k := by
  have hkQ : (k : ℚ) < (n : ℚ) := by exact_mod_cast hk
  simp only [Hc]
  apply div_pos <;> linarith

theorem Hc_lt_one (n k : ℕ) (hk : k < n) : Hc n k < 1 := by
  have hkQ : (k : ℚ) < (n : ℚ) := by exact_mod_cast hk
  simp only [Hc]
  rw [div_lt_one (by linarith)]
  linarith

theorem Fcl_nonneg (n k : ℕ) : 0 ≤ Fcl n k := by
  simp only [Fcl]
  split
  · rename_i h
    obtain ⟨hn, hk⟩ := h
    have hkj : (k : ℚ) ≤ (jIdx n : ℚ) := by exact_mod_cast hk
    have hden : (0 : ℚ) < (n : ℚ) - k + 1 := by
      have := n_sub_jIdx n
      have := ceilHalf_pos n hn
      linarith
    have := ceilHalf_pos n hn
    positivity
  · exact le_rfl

theorem Fcl_le_one (n k : ℕ) : Fcl n k ≤ 1 := by
  simp only [Fcl]
  split
  · rename_i h
    obtain ⟨hn, hk⟩ := h
    have hkj : (k : ℚ) ≤ (jIdx n : ℚ) := by exact_mod_cast hk
    have hsub := n_sub_jIdx n
    have hpos := ceilHalf_pos n hn
    have hden : (0 : ℚ) < (n : ℚ) - k + 1 := by linarith
    rw [div_le_one hden]
    linarith
  · norm_num

/-- `μ = F_n(n) = 0`, `0 < H_n(k) < 1`, and every recurrence value lies in `[0,1]`: the
counterexample satisfies the conjecture's own hypotheses, which is half the theorem. -/
theorem admissible (n k : ℕ) (hn : 4 ≤ n) (hk : k < n) :
    Fcl n n = 0 ∧ 0 < Hc n k ∧ Hc n k < 1 ∧ 0 ≤ Fcl n k ∧ Fcl n k ≤ 1 :=
  ⟨Fcl_terminal n hn, Hc_pos n k hk, Hc_lt_one n k hk, Fcl_nonneg n k, Fcl_le_one n k⟩

/-! ## The three evaluations, all exact -/

theorem three_quarters_beyond (n : ℕ) (hn : 7 ≤ n) : jIdx n < 3 * n / 4 := by
  obtain ⟨h1, h2, -, -, h5, h6, -, -⟩ := div_facts n
  simp only [jIdx]
  omega

/-- `f_n(3/4) = 0` for every `n ≥ 7` — an **exact** statement, not a limit. -/
theorem f_three_quarters (n : ℕ) (hn : 7 ≤ n) : Fcl n (3 * n / 4) = 0 :=
  Fcl_beyond n _ (three_quarters_beyond n hn)

/-- `f_n(1/2) = ⌈n/2⌉/(⌈n/2⌉+1)` exactly. -/
theorem f_half (n : ℕ) (hn : 4 ≤ n) :
    Fcl n (n / 2) = (ceilHalf n : ℚ) / ((ceilHalf n : ℚ) + 1) := by
  have hle : n / 2 ≤ jIdx n := by simp only [jIdx]; omega
  have hcond : 4 ≤ n ∧ n / 2 ≤ jIdx n := ⟨hn, hle⟩
  unfold Fcl
  rw [if_pos hcond]
  congr 1
  have h : ((n : ℚ) - ((n / 2 : ℕ) : ℚ)) = (ceilHalf n : ℚ) := by
    have hs := n_sub_jIdx n
    simp only [jIdx] at hs
    push_cast at hs
    linarith
  rw [h]

/-- Hence `1 − f_n(1/2) = 1/(⌈n/2⌉+1)`: an explicit rate, so the limit at `1/2` is `1`. -/
theorem one_sub_f_half (n : ℕ) (hn : 4 ≤ n) :
    1 - Fcl n (n / 2) = 1 / ((ceilHalf n : ℚ) + 1) := by
  rw [f_half n hn]
  have hpos : (0 : ℚ) < (ceilHalf n : ℚ) + 1 := by have := ceilHalf_pos n hn; linarith
  field_simp
  ring

/-- `f_n(1/4) = ⌈n/2⌉/(n − ⌊n/4⌋ + 1)`, whose limit is `2/3`. -/
theorem f_quarter (n : ℕ) (hn : 4 ≤ n) :
    Fcl n (n / 4) = (ceilHalf n : ℚ) / ((n : ℚ) - (n / 4 : ℕ) + 1) := by
  have hle : n / 4 ≤ jIdx n := by
    obtain ⟨h1, h2, h3, h4, -, -, -, -⟩ := div_facts n
    simp only [jIdx]
    omega
  have hcond : 4 ≤ n ∧ n / 4 ≤ jIdx n := ⟨hn, hle⟩
  unfold Fcl
  rw [if_pos hcond]

/-- `f_n(1/4) ≥ 1/2` for every `n ≥ 4`, because `2⌈n/2⌉ ≥ n ≥ n − ⌊n/4⌋ + 1`. Its limit is in
fact `2/3`; `1/2` is what a one-line `omega` argument gives, and it is all the refutation needs. -/
theorem f_quarter_ge_half (n : ℕ) (hn : 4 ≤ n) : (1 : ℚ) / 2 ≤ Fcl n (n / 4) := by
  rw [f_quarter n hn]
  obtain ⟨h1, h2, h3, h4, -, -, h7, h8⟩ := div_facts n
  have hnat : n - n / 4 + 1 ≤ 2 * ceilHalf n := by simp only [ceilHalf]; omega
  have hle : n / 4 ≤ n := Nat.div_le_self n 4
  have hcast : ((n - n / 4 : ℕ) : ℚ) = (n : ℚ) - ((n / 4 : ℕ) : ℚ) := Nat.cast_sub hle
  have hden : (n : ℚ) - (n / 4 : ℕ) + 1 ≤ 2 * (ceilHalf n : ℚ) := by
    have hc : ((n - n / 4 + 1 : ℕ) : ℚ) ≤ ((2 * ceilHalf n : ℕ) : ℚ) := by exact_mod_cast hnat
    push_cast at hc
    linarith
  have hpos : (0 : ℚ) < (n : ℚ) - (n / 4 : ℕ) + 1 := by
    have : ((n / 4 : ℕ) : ℚ) ≤ (n : ℚ) := by exact_mod_cast hle
    linarith
  rw [le_div_iff₀ hpos]
  linarith

/-! ## The refutation -/

/-- **The limit function is discontinuous at `1/2`, and no differential equation is consulted.**
Its value there is `1` — the limit of `⌈n/2⌉/(⌈n/2⌉+1)`, with the explicit gap `1/(⌈n/2⌉+1)` —
while `f_n(x)` is identically `0` for `x = 3/4` once `n ≥ 7`. A `C¹` function on `(0,1]` is
continuous, so no such limit exists. -/
theorem not_continuous_limit (n : ℕ) (hn : 7 ≤ n) :
    Fcl n (3 * n / 4) = 0 ∧ 1 - Fcl n (n / 2) = 1 / ((ceilHalf n : ℚ) + 1) :=
  ⟨f_three_quarters n hn, one_sub_f_half n (by omega)⟩

/-- **The refutation, by the write-up's sharper route.** The conjecture would force `f_n(1/4)` to
converge to the unique admissible solution's value there, which is `0` (`hODE`). But every
`f_n(1/4)` exceeds it by at least `1/2`, for every `n ≥ 4`. The hypothesis is the module's only
analytic input; `not_continuous_limit` refutes the conjecture with none at all. -/
theorem conjecture_1_false (y : ℚ → ℚ) (hODE : y (1 / 4) = 0) (n : ℕ) (hn : 4 ≤ n) :
    y (1 / 4) + 1 / 2 ≤ Fcl n (n / 4) := by
  rw [hODE, zero_add]
  exact f_quarter_ge_half n hn

end Principia.MathDB.P354674
