import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# MathDB 325243 — finite positivity forces binomial rigidity

Write-up: `mathdb-open-problems/problems/325243/solution.tex` on the `mathdb-results`
branch of `antoshashakov/Principia-Math-In-Progress`, "Finite positivity forces binomial
rigidity".  It proves **Conjecture 2.11** of Lóczi–Ketcheson (numbered 8.2 in the
published paper).

## The statement

Fix `s ≥ 1`, `t > 0`, `q ≠ 0` and reals `p 0 … p s`, and set

  `g k = ∑_{m ≤ min k s} C(s-1+k-m, s-1) · p m · q^m · (-t)^(k-m)`.

The conjecture asks whether `g 0, …, g (s+1) ≥ 0` forces `p m = c·C(s,m)·(t/q)^m`.  It
does, and the converse holds too, so the two conditions are **equivalent**; in either case
`c = p 0 = g 0` and `g k = 0` for every `k ≥ 1`.

## The one relation everything runs through

With `P z = ∑ p m q^m z^m` and `G z = P z / (1+tz)^s`, the `g k` are exactly the
coefficients of `G`, i.e. `(1+tz)^s · G z = P z`.  Coefficientwise that is

  `conv : ∀ k, ∑_{i ≤ k} D i · g (k-i) = Pc k`,

with `D i = C(s,i) t^i` (zero for `i > s`) and `Pc k = p k q^k` (zero for `k > s`).
**Every part of the theorem follows from `conv` alone**, which is why `Setup` carries it
and nothing else: deriving `conv` from the displayed formula for `g k` is precisely the
negative binomial expansion `(1+tz)^{-s} = ∑ (-1)^j C(s+j-1, s-1) t^j z^j`, a classical
identity that the write-up also invokes rather than proves.
`Campaigns/MathDB-Formalization/verify_325243.py` checks that step numerically — the
displayed `g k` satisfies `conv` across six values of `s`, twelve random parameter sets
each, for all `k ≤ 2s+3` — so the carried hypothesis is not taken on faith either.

## The argument

At `k = s+1` the right-hand side vanishes (`deg P ≤ s`), so

  `0 = ∑_{i ≤ s+1} D i · g (s+1-i)`,

in which the `i = s+1` term is `0` and every other weight `D i` is **strictly positive**.
Under the positivity hypothesis every summand is then nonnegative with total `0`, so each
is `0` and `g 1 = ⋯ = g (s+1) = 0`.  Feeding that back into `conv` at `k = m ≤ s` leaves a
single surviving term, `D m · g 0 = p m q^m`, which is the binomial form.  The converse
runs the same recursion forwards by strong induction.

## Scope (the 215 check)

* The conjecture supplies `p (s+1)` as an extra variable.  It appears in **no** `g k` for
  `k ≤ s+1`, so it is unconstrained; `Setup.p` is a function on all of `ℕ` and the
  conclusions quantify only over `m ≤ s`, which is exactly the write-up's reading ("the
  complete feasible set is the displayed ray … times `ℝ` in the last coordinate").
* `q` may be **negative**; only `q ≠ 0` is used, and the division by `q^m` at the end is
  what needs it.  `t > 0` is what makes the weights `D i` strictly positive, and that
  strictness is the whole engine of the forward direction.
-/

namespace Principia.MathDB.P325243

open Finset

/-- `D s t i = C(s,i)·tⁱ`, the coefficients of `(1+tz)^s`; zero beyond degree `s`. -/
noncomputable def D (s : ℕ) (t : ℝ) (i : ℕ) : ℝ :=
  if i ≤ s then (s.choose i : ℝ) * t ^ i else 0

/-- `Pc s q p k = p k · qᵏ`, the coefficients of `P`; zero beyond degree `s`. -/
noncomputable def Pc (s : ℕ) (q : ℝ) (p : ℕ → ℝ) (k : ℕ) : ℝ :=
  if k ≤ s then p k * q ^ k else 0

theorem D_zero_eq (s : ℕ) (t : ℝ) : D s t 0 = 1 := by
  simp [D]

theorem D_pos {s i : ℕ} {t : ℝ} (ht : 0 < t) (hi : i ≤ s) : 0 < D s t i := by
  rw [D, if_pos hi]
  have : 0 < (s.choose i : ℝ) := by
    exact_mod_cast Nat.choose_pos hi
  positivity

theorem D_of_gt {s i : ℕ} {t : ℝ} (hi : s < i) : D s t i = 0 := by
  rw [D, if_neg (by omega)]

/-- Everything carried from the source: the coefficientwise form of
`(1+tz)^s · G z = P z`. -/
structure Setup (s : ℕ) where
  t : ℝ
  q : ℝ
  ht : 0 < t
  hq : q ≠ 0
  p : ℕ → ℝ
  g : ℕ → ℝ
  conv : ∀ k : ℕ, ∑ i ∈ range (k + 1), D s t i * g (k - i) = Pc s q p k

namespace Setup

variable {s : ℕ} (S : Setup s)

/-- `g 0 = p 0`: the `k = 0` instance of `conv`. -/
theorem g_zero : S.g 0 = S.p 0 := by
  have h := S.conv 0
  simpa [D_zero_eq, Pc] using h

/-- Peeling the `i = 0` term off `conv` exposes `g k` itself. -/
theorem conv_split (k : ℕ) :
    S.g k + ∑ i ∈ range k, D s S.t (i + 1) * S.g (k - (i + 1)) = Pc s S.q S.p k := by
  have h := S.conv k
  rw [Finset.sum_range_succ'] at h
  simp only [D_zero_eq, one_mul, Nat.sub_zero] at h
  linarith

/-! ## Forward: positivity forces the ray -/

/-- The certificate: at `k = s+1` the right-hand side of `conv` vanishes. -/
theorem certificate : ∑ i ∈ range (s + 2), D s S.t i * S.g (s + 1 - i) = 0 := by
  have h := S.conv (s + 1)
  rwa [show Pc s S.q S.p (s + 1) = 0 from by rw [Pc, if_neg (by omega)]] at h

/-- Under the conjecture's hypothesis, every `g k` with `1 ≤ k ≤ s+1` vanishes. -/
theorem g_eq_zero_of_pos (hpos : ∀ k, k ≤ s + 1 → 0 ≤ S.g k) :
    ∀ k, 1 ≤ k → k ≤ s + 1 → S.g k = 0 := by
  have hterm : ∀ i ∈ range (s + 2), 0 ≤ D s S.t i * S.g (s + 1 - i) := by
    intro i hi
    rw [mem_range] at hi
    rcases le_or_gt i s with h | h
    · exact mul_nonneg (D_pos S.ht h).le (hpos _ (by omega))
    · rw [D_of_gt h, zero_mul]
  have hall := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp S.certificate
  intro k hk1 hk2
  have hi : s + 1 - k ∈ range (s + 2) := by rw [mem_range]; omega
  have := hall _ hi
  rw [show s + 1 - (s + 1 - k) = k from by omega] at this
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h (D_pos S.ht (by omega)).ne'
  · exact h

/-- **Forward direction.**  `g 0 ≥ 0` and `p m q^m = C(s,m) t^m g 0` for every `m ≤ s`:
the binomial ray, with `c = g 0 = p 0`. -/
theorem rigidity (hpos : ∀ k, k ≤ s + 1 → 0 ≤ S.g k) :
    0 ≤ S.g 0 ∧ ∀ m, m ≤ s → S.p m * S.q ^ m = (s.choose m : ℝ) * S.t ^ m * S.g 0 := by
  have hz := S.g_eq_zero_of_pos hpos
  refine ⟨hpos 0 (by omega), fun m hm => ?_⟩
  have h := S.conv m
  have hvan : ∀ i ∈ range (m + 1), i ≠ m → D s S.t i * S.g (m - i) = 0 := by
    intro i hi hne
    rw [mem_range] at hi
    rw [hz (m - i) (by omega) (by omega), mul_zero]
  rw [Finset.sum_eq_single_of_mem m (by rw [mem_range]; omega) hvan] at h
  rw [Nat.sub_self, D, if_pos hm] at h
  rw [Pc, if_pos hm] at h
  linarith [h]

/-- The conjecture's own form, obtained by dividing through by `qᵐ` — the single place
where `q ≠ 0` is needed, and the reason the hypothesis is in `Setup` at all. -/
theorem rigidity_div (hpos : ∀ k, k ≤ s + 1 → 0 ≤ S.g k) :
    0 ≤ S.g 0 ∧ ∀ m, m ≤ s → S.p m = (s.choose m : ℝ) * (S.t / S.q) ^ m * S.g 0 := by
  obtain ⟨h0, h⟩ := S.rigidity hpos
  refine ⟨h0, fun m hm => ?_⟩
  have key := h m hm
  have hq0 : S.q ≠ 0 := S.hq
  have hqm : S.q ^ m ≠ 0 := pow_ne_zero m hq0
  refine mul_right_cancel₀ hqm ?_
  rw [key, div_pow]
  field_simp

/-! ## Converse: the ray satisfies the positivity -/

/-- **Converse direction.**  On the binomial ray `g 0 = c` and `g k = 0` for `k ≥ 1`. -/
theorem ray_gives_zero (c : ℝ)
    (hp : ∀ m, m ≤ s → S.p m * S.q ^ m = c * (s.choose m : ℝ) * S.t ^ m)
    (hc : S.p 0 = c) : S.g 0 = c ∧ ∀ k, 1 ≤ k → S.g k = 0 := by
  have h0 : S.g 0 = c := by rw [S.g_zero, hc]
  refine ⟨h0, ?_⟩
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    have hsplit := S.conv_split k
    have hvan : ∀ i ∈ range k, i ≠ k - 1 →
        D s S.t (i + 1) * S.g (k - (i + 1)) = 0 := by
      intro i hi hne
      rw [mem_range] at hi
      rw [ih (k - (i + 1)) (by omega) (by omega), mul_zero]
    rw [Finset.sum_eq_single_of_mem (k - 1) (by rw [mem_range]; omega) hvan] at hsplit
    rw [show k - 1 + 1 = k from by omega, show k - k = 0 from by omega, h0] at hsplit
    rcases le_or_gt k s with hks | hks
    · rw [Pc, if_pos hks, hp k hks, D, if_pos hks] at hsplit
      linarith [hsplit]
    · rw [Pc, if_neg (by omega), D_of_gt hks] at hsplit
      linarith [hsplit]

/-- The positivity hypothesis really does hold on the ray, closing the equivalence. -/
theorem ray_pos (c : ℝ) (hc0 : 0 ≤ c)
    (hp : ∀ m, m ≤ s → S.p m * S.q ^ m = c * (s.choose m : ℝ) * S.t ^ m)
    (hc : S.p 0 = c) : ∀ k, k ≤ s + 1 → 0 ≤ S.g k := by
  obtain ⟨h0, hz⟩ := S.ray_gives_zero c hp hc
  intro k _
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [h0]; exact hc0
  · rw [hz k hk]

end Setup

end Principia.MathDB.P325243
