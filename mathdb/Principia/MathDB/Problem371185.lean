/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.

# MathDB #371185 — tie-breaking changes a player's utility by at most `min S − 1`

MathDB open problem #371185.  In the *cumulative subtraction game* on a nonempty subtraction set
`S ⊆ ℕ`, two players alternately remove `s ∈ S` stones from a heap of `h` and bank them.  Play
stops when no move is possible.  A deterministic tie-breaking convention resolves indifference
between moves that give the mover the same maximal utility; different conventions can select
different equilibria.  The source conjectures that, for fixed `S`, the resulting discrepancies in
the players' utilities stay bounded as `h` grows.

The campaign result is sharper: writing `m = min S`, **every player's discrepancy is at most
`m − 1`**, uniformly in `h` and in the two conventions.

## The shape of the proof, and what this file proves

The argument has two halves, and this file proves both.

1. `nash_close_fst` / `nash_close_snd` — a general fact about **almost-constant-sum** games: if
   every payoff sum lies in `[C, C+R]`, then any two Nash equilibria give each player utilities
   within `R`.  Four best-response and bound inequalities, no game structure at all.
2. `play_sum_le` / `play_sum_ge` — in the subtraction game the terminal remainder `r` satisfies
   `0 ≤ r < m`, because play stops only when no move fits.  Every removed stone is banked by
   exactly one player, so `u₁ + u₂ = h − r ∈ [h − m + 1, h]`.  This is `C = h − m + 1`, `R = m − 1`,
   and the bound `m − 1` is independent of `h` — which is the conjecture.

`tie_break_discrepancy` composes them.  It is stated for **any two Nash equilibria** of the game,
which is strictly more general than "any two deterministic tie-breaking conventions": backward
induction under such a convention produces a subgame-perfect, hence Nash, equilibrium of the same
game — a textbook fact about finite extensive-form games that is not restated here, and is not
needed, because quantifying over all Nash equilibria already covers every convention.

## Modelling choices

* Play is defined by **fuel-bounded structural recursion** (`playFuel`) rather than well-founded
  recursion, and `play` supplies `n` units of fuel to a heap of `n`.  Every move removes at least
  one stone, so `n` moves can never be exhausted early; the fuel is a proof device, not a cap.
* A strategy is a function from heap size to the amount to remove, and the players' strategy space
  is the **legal** strategies (`LegalStrategy`): a player who could move must name a move that is
  in `S`, positive, and no larger than the heap.  Nash equilibrium therefore quantifies over legal
  deviations only, as it must — an illegal "deviation" is not available in the game.
* `S : Set ℕ` may be infinite; only `m ∈ S` and `m` positive are used, matching the source's
  remark that only `S ∩ [1, h]` can occur.

## Sharpness

`sharp_two_by_two` exhibits, for every `R ≥ 0`, an almost-constant-sum game with two Nash
equilibria whose first-player utilities differ by exactly `R` — so the constant in the lemma cannot
be improved.  The source additionally exhibits game-level sharpness at `S = {3, 5, 8}`, `h = 23`
(utilities `(13, 10)` against `(13, 8)`, a second-player discrepancy of `2 = m − 1`); that witness
needs the backward-induction recurrence and is **not** formalized here.
-/
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Data.Set.Basic
import Mathlib.Tactic.Ring

namespace Principia.MathDB.P371185

/-! ### The almost-constant-sum equilibrium lemma -/

/-- A two-player game in strategic form with integer utilities. -/
structure Game (A B : Type*) where
  u₁ : A → B → ℤ
  u₂ : A → B → ℤ

variable {A B : Type*}

/-- `(a, b)` is a pure Nash equilibrium: neither player gains by deviating alone. -/
def Game.IsNash (G : Game A B) (a : A) (b : B) : Prop :=
  (∀ a', G.u₁ a' b ≤ G.u₁ a b) ∧ (∀ b', G.u₂ a b' ≤ G.u₂ a b)

/-- **The lemma, for player 1.**  If every payoff sum lies in `[C, C+R]`, two Nash equilibria give
player 1 utilities within `R`.  Adding the two best-response inequalities at the crossed profile
and applying the sum bounds is the whole argument. -/
theorem nash_close_fst (G : Game A B) (C R : ℤ)
    (hlo : ∀ a b, C ≤ G.u₁ a b + G.u₂ a b)
    (hhi : ∀ a b, G.u₁ a b + G.u₂ a b ≤ C + R)
    {s₁ t₁ : A} {s₂ t₂ : B}
    (hs : G.IsNash s₁ s₂) (ht : G.IsNash t₁ t₂) :
    |G.u₁ s₁ s₂ - G.u₁ t₁ t₂| ≤ R := by
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · have h1 : G.u₁ t₁ s₂ ≤ G.u₁ s₁ s₂ := hs.1 t₁
    have h2 : G.u₂ t₁ s₂ ≤ G.u₂ t₁ t₂ := ht.2 s₂
    have h3 : C ≤ G.u₁ t₁ s₂ + G.u₂ t₁ s₂ := hlo t₁ s₂
    have h4 : G.u₁ t₁ t₂ + G.u₂ t₁ t₂ ≤ C + R := hhi t₁ t₂
    linarith
  · have h1 : G.u₁ s₁ t₂ ≤ G.u₁ t₁ t₂ := ht.1 s₁
    have h2 : G.u₂ s₁ t₂ ≤ G.u₂ s₁ s₂ := hs.2 t₂
    have h3 : C ≤ G.u₁ s₁ t₂ + G.u₂ s₁ t₂ := hlo s₁ t₂
    have h4 : G.u₁ s₁ s₂ + G.u₂ s₁ s₂ ≤ C + R := hhi s₁ s₂
    linarith

/-- **The lemma, for player 2.**  The mirror image of `nash_close_fst`. -/
theorem nash_close_snd (G : Game A B) (C R : ℤ)
    (hlo : ∀ a b, C ≤ G.u₁ a b + G.u₂ a b)
    (hhi : ∀ a b, G.u₁ a b + G.u₂ a b ≤ C + R)
    {s₁ t₁ : A} {s₂ t₂ : B}
    (hs : G.IsNash s₁ s₂) (ht : G.IsNash t₁ t₂) :
    |G.u₂ s₁ s₂ - G.u₂ t₁ t₂| ≤ R := by
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · have h1 : G.u₂ s₁ t₂ ≤ G.u₂ s₁ s₂ := hs.2 t₂
    have h2 : G.u₁ s₁ t₂ ≤ G.u₁ t₁ t₂ := ht.1 s₁
    have h3 : C ≤ G.u₁ s₁ t₂ + G.u₂ s₁ t₂ := hlo s₁ t₂
    have h4 : G.u₁ t₁ t₂ + G.u₂ t₁ t₂ ≤ C + R := hhi t₁ t₂
    linarith
  · have h1 : G.u₂ t₁ s₂ ≤ G.u₂ t₁ t₂ := ht.2 s₂
    have h2 : G.u₁ t₁ s₂ ≤ G.u₁ s₁ s₂ := hs.1 t₁
    have h3 : C ≤ G.u₁ t₁ s₂ + G.u₂ t₁ s₂ := hlo t₁ s₂
    have h4 : G.u₁ s₁ s₂ + G.u₂ s₁ s₂ ≤ C + R := hhi s₁ s₂
    linarith

/-! ### Sharpness of the constant -/

/-- For `R ≥ 0`, a two-by-two almost-constant-sum game with payoff sums in `[0, R]` and two Nash
equilibria whose first-player utilities differ by exactly `R`. -/
def sharpGame (R : ℤ) : Game Bool Bool where
  u₁ := fun a b => if a && b then R else 0
  u₂ := fun a b => if a || b then 0 else R

theorem sharpGame_sum_lo (R : ℤ) (hR : 0 ≤ R) (a b : Bool) :
    0 ≤ (sharpGame R).u₁ a b + (sharpGame R).u₂ a b := by
  cases a <;> cases b <;> simp [sharpGame] <;> linarith

theorem sharpGame_sum_hi (R : ℤ) (hR : 0 ≤ R) (a b : Bool) :
    (sharpGame R).u₁ a b + (sharpGame R).u₂ a b ≤ 0 + R := by
  cases a <;> cases b <;> simp [sharpGame] <;> linarith

theorem sharpGame_nash_true (R : ℤ) (hR : 0 ≤ R) : (sharpGame R).IsNash true true := by
  refine ⟨?_, ?_⟩
  · intro a'; cases a' <;> simp [sharpGame] <;> linarith
  · intro b'; cases b' <;> simp [sharpGame]

theorem sharpGame_nash_false (R : ℤ) (hR : 0 ≤ R) : (sharpGame R).IsNash false false := by
  refine ⟨?_, ?_⟩
  · intro a'; cases a' <;> simp [sharpGame]
  · intro b'; cases b' <;> simp [sharpGame] <;> linarith

/-- **The constant `R` in the lemma is best possible.** -/
theorem sharp_two_by_two (R : ℤ) (hR : 0 ≤ R) :
    |(sharpGame R).u₁ true true - (sharpGame R).u₁ false false| = R := by
  simp [sharpGame, abs_of_nonneg hR]

/-! ### The cumulative subtraction game -/

/-- A strategy names, for each heap size, the amount to remove. -/
abbrev Strategy := ℕ → ℕ

/-- The move named by the profile `(σ, τ)` at heap `n` when it is player `p`'s turn
(`p = true` is player 1). -/
def move (σ τ : Strategy) (p : Bool) (n : ℕ) : ℕ :=
  match p with
  | true => σ n
  | false => τ n

theorem move_true (σ τ : Strategy) (n : ℕ) : move σ τ true n = σ n := rfl

theorem move_false (σ τ : Strategy) (n : ℕ) : move σ τ false n = τ n := rfl

/-- Some move is available from a heap of `n`. -/
def HasMove (S : Set ℕ) (n : ℕ) : Prop := ∃ s ∈ S, 0 < s ∧ s ≤ n

/-- A strategy is legal when it names an available move whenever one exists. -/
def Legal (S : Set ℕ) (σ : Strategy) : Prop :=
  ∀ n, HasMove S n → 0 < σ n ∧ σ n ≤ n ∧ σ n ∈ S

/-- The legal strategies — the players' actual strategy space.  An illegal "deviation" is not
available in the game, so Nash equilibrium must quantify over this type rather than over all
functions. -/
abbrev LegalStrategy (S : Set ℕ) := {σ : Strategy // Legal S σ}

/-- Bank `s` for the player to move. -/
def credit (p : Bool) (s : ℤ) (r : ℤ × ℤ) : ℤ × ℤ :=
  match p with
  | true => (r.1 + s, r.2)
  | false => (r.1, r.2 + s)

theorem credit_sum (p : Bool) (s : ℤ) (r : ℤ × ℤ) :
    (credit p s r).1 + (credit p s r).2 = r.1 + r.2 + s := by
  cases p <;> simp [credit] <;> ring

/-- The guard: the named move is playable. -/
def Playable (S : Set ℕ) (σ τ : Strategy) (p : Bool) (n : ℕ) : Prop :=
  0 < move σ τ p n ∧ move σ τ p n ≤ n ∧ move σ τ p n ∈ S

-- Play with a move budget.  Structural recursion on the budget avoids a well-founded
-- definition; `play` supplies more budget than any play can consume.  The comment cannot be a
-- doc-string: `open ... in` may not sit between a doc-string and its declaration.
open Classical in
noncomputable def playFuel (S : Set ℕ) (σ τ : Strategy) : ℕ → Bool → ℕ → ℤ × ℤ
  | 0, _, _ => (0, 0)
  | k + 1, p, n =>
      if Playable S σ τ p n then
        credit p ((move σ τ p n : ℕ) : ℤ) (playFuel S σ τ k (!p) (n - move σ τ p n))
      else (0, 0)

/-- The banked utilities of the play from a heap of `n` with `p` to move. -/
noncomputable def play (S : Set ℕ) (σ τ : Strategy) (p : Bool) (n : ℕ) : ℤ × ℤ :=
  playFuel S σ τ n p n

/-! The three unfolding lemmas.  Isolating them keeps every later proof free of `simp` on the
recursive definition. -/

theorem sum_fuel_zero (S : Set ℕ) (σ τ : Strategy) (p : Bool) (n : ℕ) :
    (playFuel S σ τ 0 p n).1 + (playFuel S σ τ 0 p n).2 = 0 := by
  simp [playFuel]

theorem sum_stop (S : Set ℕ) (σ τ : Strategy) (k : ℕ) (p : Bool) (n : ℕ)
    (hg : ¬ Playable S σ τ p n) :
    (playFuel S σ τ (k + 1) p n).1 + (playFuel S σ τ (k + 1) p n).2 = 0 := by
  simp [playFuel, hg]

theorem sum_step (S : Set ℕ) (σ τ : Strategy) (k : ℕ) (p : Bool) (n : ℕ)
    (hg : Playable S σ τ p n) :
    (playFuel S σ τ (k + 1) p n).1 + (playFuel S σ τ (k + 1) p n).2
      = (playFuel S σ τ k (!p) (n - move σ τ p n)).1
        + (playFuel S σ τ k (!p) (n - move σ τ p n)).2
        + ((move σ τ p n : ℕ) : ℤ) := by
  have hunfold : playFuel S σ τ (k + 1) p n
      = credit p ((move σ τ p n : ℕ) : ℤ) (playFuel S σ τ k (!p) (n - move σ τ p n)) := by
    simp [playFuel, hg]
  rw [hunfold]
  exact credit_sum _ _ _

/-- **The upper bound.**  At most every stone is banked. -/
theorem playFuel_sum_le (S : Set ℕ) (σ τ : Strategy) :
    ∀ (k : ℕ) (p : Bool) (n : ℕ),
      (playFuel S σ τ k p n).1 + (playFuel S σ τ k p n).2 ≤ (n : ℤ) := by
  intro k
  induction k with
  | zero =>
    intro p n
    rw [sum_fuel_zero]
    positivity
  | succ k ih =>
    intro p n
    by_cases hg : Playable S σ τ p n
    · have h1 : 0 < move σ τ p n := hg.1
      have h2 : move σ τ p n ≤ n := hg.2.1
      have hIH := ih (!p) (n - move σ τ p n)
      have hs := sum_step S σ τ k p n hg
      omega
    · rw [sum_stop S σ τ k p n hg]
      positivity

/-- **The lower bound.**  Play stops only when no move fits, so fewer than `m` stones survive. -/
theorem playFuel_sum_ge (S : Set ℕ) (σ τ : Strategy) (hσ : Legal S σ) (hτ : Legal S τ)
    (m : ℕ) (hmem : m ∈ S) (hpos : 0 < m) :
    ∀ (k : ℕ) (p : Bool) (n : ℕ), n ≤ k →
      (n : ℤ) - (m : ℤ) + 1 ≤ (playFuel S σ τ k p n).1 + (playFuel S σ τ k p n).2 := by
  intro k
  induction k with
  | zero =>
    intro p n hn
    have hn0 : n = 0 := Nat.le_zero.mp hn
    have hm1 : (1 : ℤ) ≤ (m : ℤ) := by exact_mod_cast hpos
    rw [sum_fuel_zero, hn0]
    push_cast
    linarith
  | succ k ih =>
    intro p n hn
    by_cases hg : Playable S σ τ p n
    · have h1 : 0 < move σ τ p n := hg.1
      have h2 : move σ τ p n ≤ n := hg.2.1
      have hIH := ih (!p) (n - move σ τ p n) (by omega)
      have hs := sum_step S σ τ k p n hg
      omega
    · have hnm : n < m := by
        by_contra hc
        have hhas : HasMove S n := ⟨m, hmem, hpos, Nat.not_lt.mp hc⟩
        refine hg ?_
        cases p with
        | true =>
          have hl := hσ n hhas
          exact ⟨hl.1, hl.2.1, hl.2.2⟩
        | false =>
          have hl := hτ n hhas
          exact ⟨hl.1, hl.2.1, hl.2.2⟩
      have hmn : (n : ℤ) + 1 ≤ (m : ℤ) := by exact_mod_cast hnm
      rw [sum_stop S σ τ k p n hg]
      linarith

theorem play_sum_le (S : Set ℕ) (σ τ : Strategy) (p : Bool) (n : ℕ) :
    (play S σ τ p n).1 + (play S σ τ p n).2 ≤ (n : ℤ) :=
  playFuel_sum_le S σ τ n p n

theorem play_sum_ge (S : Set ℕ) (σ τ : Strategy) (hσ : Legal S σ) (hτ : Legal S τ)
    (m : ℕ) (hmem : m ∈ S) (hpos : 0 < m) (p : Bool) (n : ℕ) :
    (n : ℤ) - (m : ℤ) + 1 ≤ (play S σ τ p n).1 + (play S σ τ p n).2 :=
  playFuel_sum_ge S σ τ hσ hτ m hmem hpos n p n le_rfl

/-- The strategic form of the subtraction game from a heap of `h`. -/
noncomputable def game (S : Set ℕ) (h : ℕ) : Game (LegalStrategy S) (LegalStrategy S) where
  u₁ := fun σ τ => (play S σ.1 τ.1 true h).1
  u₂ := fun σ τ => (play S σ.1 τ.1 true h).2

/-! ### The conjecture -/

/-- **MathDB #371185.**  For a subtraction set `S` with least positive element `m`, any two Nash
equilibria of the cumulative subtraction game from any heap `h` give each player utilities within
`m − 1`.  The bound does not depend on `h`, which is the source's conjecture; every deterministic
tie-breaking convention yields a Nash equilibrium by backward induction, so this covers every pair
of conventions. -/
theorem tie_break_discrepancy (S : Set ℕ) (m : ℕ) (hmem : m ∈ S) (hpos : 0 < m) (h : ℕ)
    {σ₁ τ₁ σ₂ τ₂ : LegalStrategy S}
    (hs : (game S h).IsNash σ₁ σ₂) (ht : (game S h).IsNash τ₁ τ₂) :
    |(game S h).u₁ σ₁ σ₂ - (game S h).u₁ τ₁ τ₂| ≤ (m : ℤ) - 1 ∧
      |(game S h).u₂ σ₁ σ₂ - (game S h).u₂ τ₁ τ₂| ≤ (m : ℤ) - 1 := by
  have hlo : ∀ (a b : LegalStrategy S),
      ((h : ℤ) - (m : ℤ) + 1) ≤ (game S h).u₁ a b + (game S h).u₂ a b :=
    fun a b => play_sum_ge S a.1 b.1 a.2 b.2 m hmem hpos true h
  have hhi : ∀ (a b : LegalStrategy S),
      (game S h).u₁ a b + (game S h).u₂ a b ≤ ((h : ℤ) - (m : ℤ) + 1) + ((m : ℤ) - 1) := by
    intro a b
    have hle := play_sum_le S a.1 b.1 true h
    have harith : ((h : ℤ) - (m : ℤ) + 1) + ((m : ℤ) - 1) = (h : ℤ) := by ring
    rw [harith]
    exact hle
  exact ⟨nash_close_fst (game S h) _ _ hlo hhi hs ht,
    nash_close_snd (game S h) _ _ hlo hhi hs ht⟩

section Existence

/-! ### The players' strategy space is nonempty

`LegalStrategy S` is the type the game is played over, and the row's equilibrium statements
quantify over it.  **Over an empty type every strategy profile is an equilibrium**, so the
row's claim needed `Legal` to be inhabited, and nothing produced a legal strategy.

The witness is the obvious one: whenever a move is available, play the one the availability
proof names; otherwise play `0`.  That is legal by construction, since `Legal` only constrains
`σ n` at those `n` where `HasMove S n` holds.
-/

open Classical in
/-- A legal strategy: play whatever move the availability proof supplies. -/
noncomputable def legalWitness (S : Set ℕ) : Strategy :=
  fun n => if h : HasMove S n then h.choose else 0

theorem legal_legalWitness (S : Set ℕ) : Legal S (legalWitness S) := by
  intro n hn
  simp only [legalWitness, dif_pos hn]
  obtain ⟨hmem, hpos, hle⟩ := hn.choose_spec
  exact ⟨hpos, hle, hmem⟩

/-- **The legal strategies form a nonempty type**, for every rule set `S`. -/
theorem nonempty_legalStrategy (S : Set ℕ) : Nonempty (LegalStrategy S) :=
  ⟨⟨legalWitness S, legal_legalWitness S⟩⟩

end Existence

end Principia.MathDB.P371185
