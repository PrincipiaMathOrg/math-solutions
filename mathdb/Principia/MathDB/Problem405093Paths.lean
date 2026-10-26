import Mathlib

/-!
# MathDB #405093 — counting axis-parallel lattice paths by compositions

Write-up: `antoshashakov/Principia-Math-In-Progress`, branch `mathdb-results`,
`mathdb-open-problems/problems/405093/solution.tex`.  A step is `(u, 0)` or `(0, u)` with `u ≥ 1`.
`paths a b ℓ` counts step sequences of length `ℓ` from `(0, 0)` to `(a, b)`, defined by the first
step: after a horizontal step of length `a − u` the rest runs from `(0,0)` to `(u, b)`.  Likewise
`comp n k` counts compositions of `n` into `k` positive parts, by the first part.

`paths_eq` is the write-up's equation (2) in the form
`paths a b ℓ = ∑_{h+v=ℓ} C(ℓ, h) comp(a, h) comp(b, v)` (choose the step directions, then the two
compositions), proved from the two recursions by Pascal's rule.  Checked in Python against both the
recursion and the closed form for `a, b ≤ 6`, `ℓ ≤ 11`.  The lattice-path theorem is the consumer.
-/

namespace Principia.MathDB.P405093

open Finset

/-- Compositions of `n` into `k` positive parts, counted by the first part. -/
def comp : ℕ → ℕ → ℕ
  | n, 0 => if n = 0 then 1 else 0
  | n, k + 1 => ∑ u ∈ range n, comp u k

/-- Axis-parallel paths of `ℓ` positive steps from `(0,0)` to `(a,b)`, counted by the first step. -/
def paths : ℕ → ℕ → ℕ → ℕ
  | a, b, 0 => if a = 0 ∧ b = 0 then 1 else 0
  | a, b, l + 1 => ∑ u ∈ range a, paths u b l + ∑ u ∈ range b, paths a u l

theorem comp_succ (n k : ℕ) : comp n (k + 1) = ∑ u ∈ range n, comp u k := rfl

theorem paths_succ (a b l : ℕ) :
    paths a b (l + 1) = ∑ u ∈ range a, paths u b l + ∑ u ∈ range b, paths a u l := rfl

/-- The write-up's equation (2): paths counted by step directions and two compositions. -/
theorem paths_eq : ∀ l a b : ℕ,
    paths a b l = ∑ p ∈ antidiagonal l, l.choose p.1 * comp a p.1 * comp b p.2 := by
  intro l
  induction l with
  | zero =>
    intro a b
    by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> simp [paths, comp, ha, hb]
  | succ l ih =>
    intro a b
    have hs1 : ∑ u ∈ range a, paths u b l
        = ∑ p ∈ antidiagonal l, l.choose p.1 * comp a (p.1 + 1) * comp b p.2 := by
      simp only [ih, comp_succ]
      rw [Finset.sum_comm]
      refine sum_congr rfl fun p _ => ?_
      rw [Finset.mul_sum, Finset.sum_mul]
    have hs2 : ∑ u ∈ range b, paths a u l
        = ∑ p ∈ antidiagonal l, l.choose p.1 * comp a p.1 * comp b (p.2 + 1) := by
      simp only [ih, comp_succ]
      rw [Finset.sum_comm]
      refine sum_congr rfl fun p _ => ?_
      rw [Finset.mul_sum]
    rw [paths_succ, hs1, hs2]
    -- expand the target by the first coordinate and Pascal's rule
    rw [Finset.Nat.sum_antidiagonal_succ]
    simp only [Nat.choose_succ_succ, add_mul, Finset.sum_add_distrib, Nat.succ_eq_add_one]
    -- the sum `∑_{AD(l+1)} C(l, q.1) comp a q.1 comp b q.2`, expanded both ways
    have g1 := Finset.Nat.sum_antidiagonal_succ
      (f := fun q : ℕ × ℕ => l.choose q.1 * comp a q.1 * comp b q.2) (n := l)
    have g2 := Finset.Nat.sum_antidiagonal_succ'
      (f := fun q : ℕ × ℕ => l.choose q.1 * comp a q.1 * comp b q.2) (n := l)
    simp only [Nat.choose_zero_right, Nat.choose_succ_self, zero_mul, zero_add, one_mul,
      Nat.succ_eq_add_one] at g1 g2
    simp only [Nat.choose_zero_right, one_mul, Nat.succ_eq_add_one]
    omega

end Principia.MathDB.P405093
