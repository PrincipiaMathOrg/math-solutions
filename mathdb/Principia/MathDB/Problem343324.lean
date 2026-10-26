import Mathlib

/-!
# MathDB #343324 — the parity conjecture for the Navarrete–Orellana sequences

Write-up `mathdb-open-problems/problems/343324/solution.tex`,
*Odd fixed points of the Navarrete–Orellana greedy sequences*, 18 September 2026.

For an odd prime `p`, the source sets `q_p(n) = ∑_{j<n} j·p` and defines `a_p(1) = 1`, with
`a_p(n)` for `n ≥ 2` the least positive divisor of `q_p(n)` not already used.  Its Conjecture 3.1
asserts that `a_p(n) = n` can occur only at odd `n`.

The obstruction is already in the divisibility condition, and needs neither primality nor the
greedy rule:

**If `m` is odd, `0 < n`, and `n ∣ q_m(n)`, then `n` is odd.**

Because `2·q_m(n) = m·n·(n−1)`, writing `q_m(n) = n·b` and cancelling `n > 0` gives
`m·(n−1) = 2·b`; since `m` is odd, `2 ∣ n−1`, so `n` is odd.

## What the greedy rule contributes, and what it does not

`main` takes as a hypothesis only that `a k ∣ q_p k` — the one consequence of the defining rule
the argument uses.  Primality of `p` is **not** needed (only oddness), and the greedy selection is
not needed at all; stating it that way is the point, since it shows the conjecture holds for a far
wider class than it was posed for.  `n = 1` is included: `q_m(1) = 0` and everything divides `0`.

Everything is over `ℕ` and division is avoided entirely — `2 · q` is compared with `m·n·(n−1)`
via `Finset.sum_range_id_mul_two`, so no truncating `ℕ` division ever appears.

Checked in Python before formalizing: `q_p(n) = p·C(n,2)` for several `p` and all `n < 40`; no
counterexample to the core claim for odd `m < 40` and `n < 200`; and, for `p = 3`, the greedy
sequence's fixed points up to 60 are `1, 5, 7, 11, 13, 19, 23, 29, 31, 37, 41, 43, 47, 53, 55, 59`
— all odd.
-/

namespace Principia.MathDB.P343324

/-- `q_m(n) = ∑_{j<n} j·m`, the source's quantity. -/
def qm (m n : ℕ) : ℕ := ∑ j ∈ Finset.range n, j * m

/-- `2·q_m(n) = m·n·(n−1)`, with no division anywhere. -/
theorem two_mul_qm (m n : ℕ) : 2 * qm m n = m * (n * (n - 1)) := by
  unfold qm
  rw [← Finset.sum_mul]
  calc 2 * ((∑ j ∈ Finset.range n, j) * m)
      = m * ((∑ j ∈ Finset.range n, j) * 2) := by ring
    _ = m * (n * (n - 1)) := by rw [Finset.sum_range_id_mul_two]

/-- **The arithmetic core.**  Oddness of `m` alone forces any `n` dividing `q_m(n)` to be odd. -/
theorem odd_of_dvd (m n : ℕ) (hm : Odd m) (hn : 0 < n) (hdvd : n ∣ qm m n) : Odd n := by
  obtain ⟨b, hb⟩ := hdvd
  have h2 : m * (n * (n - 1)) = n * (2 * b) := by
    rw [← two_mul_qm, hb]; ring
  have hcancel : m * (n - 1) = 2 * b := by
    refine Nat.eq_of_mul_eq_mul_left hn ?_
    calc n * (m * (n - 1)) = m * (n * (n - 1)) := by ring
      _ = n * (2 * b) := h2
  have heven : Even (m * (n - 1)) := ⟨b, by omega⟩
  rcases Nat.even_mul.mp heven with h | h
  · obtain ⟨r, hr⟩ := h
    obtain ⟨k, hk⟩ := hm
    omega
  · obtain ⟨c, hc⟩ := h
    exact Nat.odd_iff.mpr (by omega)

/-- **MathDB #343324 — Conjecture 3.1 holds.**  Every fixed point of the sequence is odd.

The only property of the greedy rule used is `a k ∣ q_p k`; primality of `p` is not used, only
oddness.  So the conclusion is strictly more general than the conjecture as posed. -/
theorem main (p : ℕ) (hp : Odd p) (a : ℕ → ℕ)
    (hrule : ∀ k, a k ∣ qm p k) (n : ℕ) (hn : 0 < n) (hfix : a n = n) : Odd n := by
  refine odd_of_dvd p n hp hn ?_
  have h := hrule n
  rwa [hfix] at h

end Principia.MathDB.P343324
