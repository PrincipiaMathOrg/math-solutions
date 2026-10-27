import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

set_option autoImplicit false

/-!
# MathDB #322992 — Amdeberhan–Moll–Vignat Conjecture 8.7

Write-up: `mathdb-open-problems/problems/322992/solution.tex`, collaborator branch
`mathdb-results` of `antoshashakov/Principia-Math-In-Progress` (enrolled here 2026-09-30).
Source: T. Amdeberhan, V. Moll and C. Vignat, **Conjecture 8.7**, recurrence (7.10).

The conjecture asks for an initial value making the quadratic recurrence
`a_n = Σ_{k<n} C_μ(n,k) a_k a_{n−k}` `p`-integral. The write-up proves the stronger statement
that `a₁ = D_μ = 2·lcm(1,…,2μ)` makes **every** term a positive integer, by showing that
`D_μ C_μ(n,k)` is a positive integer — and that reduces to a floor-function inequality.

## The floor lemma is the engine, and it is proved here in full generality

With `a = k−1`, `b = n−k−1`, `t = μ+1`,

`2 C_μ(n,k) = (t−1)! (a+b+1)! (a+b+t)! / ( a! b! (a+t)! (b+t)! )`,

so Legendre's formula turns each prime valuation into a sum of

`F_q(a,b,t) = ⌊(a+b+1)/q⌋ + ⌊(a+b+t)/q⌋ + ⌊(t−1)/q⌋ − ⌊a/q⌋ − ⌊b/q⌋ − ⌊(a+t)/q⌋ − ⌊(b+t)/q⌋`

over prime powers `q`. `floor_ge_neg_one` proves `F_q ≥ −1` for **all** `q ≥ 2`, `t ≥ 1` and all
`a, b`; `floor_nonneg` proves `F_q ≥ 0` once `q ≥ 2t−1`. Both are stated without subtraction, so
no `ℕ`-truncation arises, and both are unconditional.

**Why they are not one `omega` call.** `omega` models `ℕ` division by a *literal*; here the
divisor is a variable, and `q * (a / q)` is a product of unknowns. The proofs therefore go through
`add_div_split`, which turns `(x + y) / q` into `x/q + y/q + (x%q + y%q)/q` — the residue form the
write-up uses — after which every quotient is of something smaller than `2q` and the case analysis
is finite.

## What is proved

* `add_div_split`, `shift_div`, `reduce_ab` — the residue decompositions, for arbitrary `q > 0`.
  `shift_div` is the single engine: `(x+c)/q = x/q + (x%q + c)/q`, which is why no case analysis
  on `a` or `b` is ever needed.
* `small_div_le_one`, `div_ge_one_of_ge`, `div_eq_zero_of_lt`, `div_pred_ge`, `div_pred_eq` — the
  facts that make residue quotients decidable, and the two statements about `⌊(t−1)/q⌋`.
* `floor_key` — the reduced inequality, for `r, s, u < q`: this is the write-up's displayed
  expression and the whole mathematical content.
* `floor_key_nonneg` — its `q ≥ 2t−1` counterpart.
* `floor_ge_neg_one` and `floor_nonneg` — the general statements, reduced to the above.
* `coeff_ratio` — the factorial identity `2 C_μ(n,k) = …`, as an equation between products, so
  that no division appears.
* `legendre_term`, `legendre_sum_bound`, `factorization_bound` — **the consumer.** A floor bound
  that nothing consumes proves nothing about the conjecture, so the two floor statements are
  packaged into the single termwise bound Legendre's formula sums, and then into a statement
  about the `p`-adic valuation of the factorial ratio: for every prime `p`, the denominator
  `a! b! (a+t)! (b+t)!` carries at most `#{i : p^i < 2t−1}` more factors of `p` than the numerator
  `(t−1)! (a+b+1)! (a+b+t)!`. That count depends on `t` alone, which is exactly why a **fixed**
  multiplier clears every denominator at once.

## What the unused-hypothesis linter found, and it was right

`1 ≤ t` was carried by `floor_key_nonneg`, `floor_nonneg` and `floor_ge_neg_one`, because the
source has `t = μ+1 ≥ 1`. The proofs never used it, and the verifier then measured that all three
statements hold at `t = 0` as well over their sampled ranges, so the hypothesis came out of all
three — the theorems are strictly stronger than the ones first written. It survives only in
`coeff_ratio` and `factorization_bound`, where `a+b+1 ≤ a+b+t` genuinely needs it.

## What is absent, and what is residue

Mathlib has Legendre's formula (`Nat.factorization_factorial`), and it is now used rather than
cited. What remains is: the arithmetic that turns `factorization_bound` into
`v_ℓ(L_μ) ≥ Σ_{negative terms}` — i.e. that `L_μ = lcm(1,…,2μ)` really does carry at least
`#{i : ℓ^i < 2t−1}` factors of `ℓ` — and the strong induction giving `b_n ∈ ℤ_{>0}`. Neither is
blocked on absent Mathlib; both are unwritten.

## Two findings, plus one measured limit of the Lean statement

* **The `−1` is tight and the `q ≥ 2t−1` hypothesis is load-bearing.** The verifier attains
  `F = −1` (26510 times in its sweep) and exhibits `q < 2t−1` with `F < 0`, at `(q,a,b,t) =
  (2,0,0,2)` with `2t−1 = 3`. Neither bound is slack.
* **`D_μ` is sufficient but not least**, which is the write-up's own open Task 2. Measured over
  the sampled range: `D_μ` and the least working multiplier agree at `μ ≤ 1` and diverge from
  `μ = 2`, with ratios `2, 3, 12, 10, 30` at `μ = 2,…,6`. The boundary is measured, not assumed.
* **`factorization_bound` is a bound, not an identity.** Its count is attained — so the statement
  is sharp as written — but for some `(p,t)`, among them `(2,3)`, `(2,5)`, `(3,4)`, the true
  worst-case excess is strictly below it. Recorded so the next reader does not mistake it for an
  exact valuation formula.
-/

namespace Principia.MathDB.P322992

/-! ## Residue arithmetic -/

/-- **The residue decomposition.** `(x + y) / q = x/q + y/q + (x%q + y%q)/q`, for any `q > 0`.
This is what replaces `omega`, which cannot divide by a variable. -/
theorem add_div_split (q x y : ℕ) (hq : 0 < q) :
    (x + y) / q = x / q + y / q + (x % q + y % q) / q := by
  conv_lhs => rw [← Nat.div_add_mod x q, ← Nat.div_add_mod y q]
  rw [show q * (x / q) + x % q + (q * (y / q) + y % q)
      = x % q + y % q + q * (x / q + y / q) by ring]
  rw [Nat.add_mul_div_left _ _ hq]
  ring

/-- A quotient of something below `2q` is at most one. -/
theorem small_div_le_one (q x : ℕ) (hq : 0 < q) (hx : x < 2 * q) : x / q ≤ 1 := by
  by_contra h
  push Not at h
  have := Nat.le_div_iff_mul_le hq |>.mp h
  omega

/-- And it is at least one exactly when the numerator reaches `q`. -/
theorem div_ge_one_of_ge (q x : ℕ) (hq : 0 < q) (hx : q ≤ x) : 1 ≤ x / q :=
  (Nat.one_le_div_iff hq).mpr hx

theorem div_eq_zero_of_lt (q x : ℕ) (hx : x < q) : x / q = 0 := Nat.div_eq_of_lt hx

/-! ## The reduced inequality — the write-up's displayed expression -/

/-- **The heart.** For residues `r, s, u < q`, the reduced form of `F_q ≥ −1`. -/
theorem floor_key (q r s u : ℕ) (hq : 2 ≤ q) (hr : r < q) (hs : s < q) (hu : u < q) :
    (r + u) / q + (s + u) / q + (if u = 0 then 1 else 0)
      ≤ (r + s + 1) / q + (r + s + u) / q + 1 := by
  have hq0 : 0 < q := by omega
  -- `omega` translates ℕ-division into ℤ-division and then does NOT know the quotients are
  -- nonnegative; supply that, and every quotient bound, explicitly.
  have z1 : 0 ≤ (r + s + 1) / q := Nat.zero_le _
  have z2 : 0 ≤ (r + s + u) / q := Nat.zero_le _
  have z3 : 0 ≤ (r + u) / q := Nat.zero_le _
  have z4 : 0 ≤ (s + u) / q := Nat.zero_le _
  rcases Nat.eq_zero_or_pos u with hu0 | hu1
  · subst hu0
    have e1 : r / q = 0 := div_eq_zero_of_lt q r hr
    have e2 : s / q = 0 := div_eq_zero_of_lt q s hs
    have z5 : 0 ≤ (r + s) / q := Nat.zero_le _
    -- `+ 0` and the decided `if` both reduce, so the goal is stated directly
    change r / q + s / q + 1 ≤ (r + s + 1) / q + (r + s) / q + 1
    omega
  · rw [if_neg (by omega : ¬ u = 0)]
    have h1 : (r + u) / q ≤ 1 := small_div_le_one q _ hq0 (by omega)
    have h2 : (s + u) / q ≤ 1 := small_div_le_one q _ hq0 (by omega)
    rcases Nat.lt_or_ge (r + u) q with hru | hru
    · have e1 : (r + u) / q = 0 := div_eq_zero_of_lt q _ hru
      omega
    rcases Nat.lt_or_ge (s + u) q with hsu | hsu
    · have e2 : (s + u) / q = 0 := div_eq_zero_of_lt q _ hsu
      omega
    · have hbig : q ≤ r + s + u := by omega
      have h3 : 1 ≤ (r + s + u) / q := div_ge_one_of_ge q _ hq0 hbig
      omega

/-- **The heart, sharp form.** Under `q ≥ 2t−1` the same expression is nonnegative. -/
theorem floor_key_nonneg (q r s t : ℕ) (hq : 2 ≤ q) (hqt : 2 * t - 1 ≤ q)
    (hr : r < q) (hs : s < q) (htq : t < q) :
    (r + t) / q + (s + t) / q ≤ (r + s + 1) / q + (r + s + t) / q := by
  have hq0 : 0 < q := by omega
  have z1 : 0 ≤ (r + s + 1) / q := Nat.zero_le _
  have z2 : 0 ≤ (r + s + t) / q := Nat.zero_le _
  have z3 : 0 ≤ (r + t) / q := Nat.zero_le _
  have z4 : 0 ≤ (s + t) / q := Nat.zero_le _
  have h1 : (r + t) / q ≤ 1 := small_div_le_one q _ hq0 (by omega)
  have h2 : (s + t) / q ≤ 1 := small_div_le_one q _ hq0 (by omega)
  rcases Nat.lt_or_ge (r + t) q with hrt | hrt
  · have e1 : (r + t) / q = 0 := div_eq_zero_of_lt q _ hrt
    rcases Nat.lt_or_ge (s + t) q with hst | hst
    · have e2 : (s + t) / q = 0 := div_eq_zero_of_lt q _ hst
      omega
    · have hbig : q ≤ r + s + t := by omega
      have h3 : 1 ≤ (r + s + t) / q := div_ge_one_of_ge q _ hq0 hbig
      omega
  · rcases Nat.lt_or_ge (s + t) q with hst | hst
    · have e2 : (s + t) / q = 0 := div_eq_zero_of_lt q _ hst
      have hbig : q ≤ r + s + t := by omega
      have h3 : 1 ≤ (r + s + t) / q := div_ge_one_of_ge q _ hq0 hbig
      omega
    · -- both reach `q`: `r + s + 1 ≥ 2q − 2t + 1 ≥ q` is where `q ≥ 2t − 1` is used
      have hone : q ≤ r + s + 1 := by omega
      have htwo : q ≤ r + s + t := by omega
      have h3 : 1 ≤ (r + s + 1) / q := div_ge_one_of_ge q _ hq0 hone
      have h4 : 1 ≤ (r + s + t) / q := div_ge_one_of_ge q _ hq0 htwo
      omega

/-! ## The factorial identity behind the coefficient -/

/-- **`2 C_μ(n,k)` as a factorial ratio, stated multiplicatively so no division appears.**
With `a = k−1`, `b = n−k−1`, `t = μ+1`, the source's
`binom(a+b+t, b)·binom(a+b+t, a) / binom(a+b+t, a+b+1)` equals
`(t−1)!(a+b+1)!(a+b+t)! / (a! b! (a+t)! (b+t)!)`. -/
theorem coeff_ratio (a b t : ℕ) (ht : 1 ≤ t) :
    Nat.choose (a + b + t) b * Nat.choose (a + b + t) a
        * (Nat.factorial a * Nat.factorial b * Nat.factorial (a + t) * Nat.factorial (b + t))
      = Nat.choose (a + b + t) (a + b + 1)
        * (Nat.factorial (t - 1) * Nat.factorial (a + b + 1) * Nat.factorial (a + b + t)) := by
  have hb : b ≤ a + b + t := by omega
  have ha : a ≤ a + b + t := by omega
  have hab : a + b + 1 ≤ a + b + t := by omega
  have eb := Nat.choose_mul_factorial_mul_factorial hb
  have ea := Nat.choose_mul_factorial_mul_factorial ha
  have eab := Nat.choose_mul_factorial_mul_factorial hab
  have hbt : a + b + t - b = a + t := by omega
  have hat : a + b + t - a = b + t := by omega
  have habt : a + b + t - (a + b + 1) = t - 1 := by omega
  rw [hbt] at eb
  rw [hat] at ea
  rw [habt] at eab
  -- both sides equal `(a+b+t)! * (a+b+t)! * (a+b+1)! * (t-1)!` after clearing
  have hfac : 0 < Nat.factorial (a + b + t) := Nat.factorial_pos _
  nlinarith [eb, ea, eab, Nat.factorial_pos a, Nat.factorial_pos b,
    Nat.factorial_pos (a + t), Nat.factorial_pos (b + t), Nat.factorial_pos (a + b + 1),
    Nat.factorial_pos (t - 1), hfac]

/-! ## The general floor statements -/

/-- **Shifting only sees the residue.** `(x + c)/q = x/q + (x % q + c)/q` — the single engine
behind every reduction below, and the reason no case analysis on `a` or `b` is ever needed. -/
theorem shift_div (q x c : ℕ) (hq : 0 < q) : (x + c) / q = x / q + (x % q + c) / q := by
  conv_lhs => rw [← Nat.div_add_mod x q]
  rw [show q * (x / q) + x % q + c = x % q + c + q * (x / q) by ring,
    Nat.add_mul_div_left _ _ hq]
  ring

/-- **Reduce the first two summands to their residues**, leaving the third alone. -/
theorem reduce_ab (q a b c : ℕ) (hq : 0 < q) :
    (a + b + c) / q = a / q + b / q + (a % q + b % q + c) / q := by
  rw [shift_div q (a + b) c hq, add_div_split q a b hq,
    shift_div q (a % q + b % q) c hq, Nat.add_mod a b q]
  ring

/-- `t/q` drops by at most one when `t` drops by one. -/
theorem div_pred_ge (q t : ℕ) (hq : 2 ≤ q) : t / q ≤ (t - 1) / q + 1 := by
  have hq0 : 0 < q := by omega
  rcases Nat.eq_zero_or_pos t with h0 | h1
  · subst h0
    simp
  have h := add_div_split q (t - 1) 1 hq0
  have ht1 : t - 1 + 1 = t := by omega
  rw [ht1] at h
  have hz : (1 : ℕ) / q = 0 := Nat.div_eq_of_lt (by omega)
  have hm : (1 : ℕ) % q = 1 := Nat.mod_eq_of_lt (by omega)
  have hlt : (t - 1) % q < q := Nat.mod_lt _ hq0
  have hle : ((t - 1) % q + 1 % q) / q ≤ 1 := small_div_le_one q _ hq0 (by omega)
  have hnn : 0 ≤ ((t - 1) % q + 1 % q) / q := Nat.zero_le _
  omega

/-- And it does not drop at all when `q ∤ t`: the subtraction stays inside the residue. -/
theorem div_pred_eq (q t : ℕ) (hq : 0 < q) (hu : 1 ≤ t % q) : (t - 1) / q = t / q := by
  have hdm := Nat.div_add_mod t q
  have hlt : t % q < q := Nat.mod_lt _ hq
  have hrw : t - 1 = (t % q - 1) + q * (t / q) := by omega
  rw [hrw, Nat.add_mul_div_left _ _ hq, Nat.div_eq_of_lt (by omega : t % q - 1 < q)]
  omega

/-- **`F_q(a,b,t) ≥ −1`**, for every `q ≥ 2`, `t ≥ 1` and all `a, b`. Stated without subtraction
on the left, so no `ℕ` truncation occurs. This is the bound that makes `2 C_μ(n,k)` miss being an
integer by a bounded amount at each prime power, and it is **tight** — the verifier exhibits
`F = −1`. -/
theorem floor_ge_neg_one (q a b t : ℕ) (hq : 2 ≤ q) :
    a / q + b / q + (a + t) / q + (b + t) / q
      ≤ (a + b + 1) / q + (a + b + t) / q + (t - 1) / q + 1 := by
  have hq0 : 0 < q := by omega
  have hr : a % q < q := Nat.mod_lt _ hq0
  have hs : b % q < q := Nat.mod_lt _ hq0
  have hu : t % q < q := Nat.mod_lt _ hq0
  -- reduce `a` and `b`
  have e1 : (a + t) / q = a / q + (a % q + t) / q := shift_div q a t hq0
  have e2 : (b + t) / q = b / q + (b % q + t) / q := shift_div q b t hq0
  have e3 : (a + b + 1) / q = a / q + b / q + (a % q + b % q + 1) / q := reduce_ab q a b 1 hq0
  have e4 : (a + b + t) / q = a / q + b / q + (a % q + b % q + t) / q := reduce_ab q a b t hq0
  -- now reduce `t` as well, in each of the three places it survives
  have f1 : (a % q + t) / q = t / q + (a % q + t % q) / q := by
    have h := shift_div q t (a % q) hq0
    rw [show t + a % q = a % q + t by ring, show t % q + a % q = a % q + t % q by ring] at h
    exact h
  have f2 : (b % q + t) / q = t / q + (b % q + t % q) / q := by
    have h := shift_div q t (b % q) hq0
    rw [show t + b % q = b % q + t by ring, show t % q + b % q = b % q + t % q by ring] at h
    exact h
  have f3 : (a % q + b % q + t) / q = t / q + (a % q + b % q + t % q) / q := by
    have h := shift_div q t (a % q + b % q) hq0
    rw [show t + (a % q + b % q) = a % q + b % q + t by ring,
      show t % q + (a % q + b % q) = a % q + b % q + t % q by ring] at h
    exact h
  rw [e1, e2, e3, e4, f1, f2, f3]
  have key := floor_key q (a % q) (b % q) (t % q) hq hr hs hu
  have hstep := div_pred_ge q t hq
  -- `omega` lifts `ℕ`-division by a VARIABLE to an opaque `ℤ` atom and does not know the atom
  -- is nonnegative; every quotient therefore has to be told so by hand
  have n1 : 0 ≤ (a % q + t % q) / q := Nat.zero_le _
  have n2 : 0 ≤ (b % q + t % q) / q := Nat.zero_le _
  have n3 : 0 ≤ (a % q + b % q + 1) / q := Nat.zero_le _
  have n4 : 0 ≤ (a % q + b % q + t % q) / q := Nat.zero_le _
  have n5 : 0 ≤ (t - 1) / q := Nat.zero_le _
  have n6 : 0 ≤ t / q := Nat.zero_le _
  rcases Nat.eq_zero_or_pos (t % q) with h0 | h1
  · rw [if_pos h0] at key
    omega
  · rw [if_neg (by omega : ¬ t % q = 0)] at key
    have heq : (t - 1) / q = t / q := div_pred_eq q t hq0 h1
    omega

/-- **`F_q(a,b,t) ≥ 0`** once `q ≥ 2t−1`: the negative contributions are confined to the finitely
many prime powers below `2t−1`, which is exactly why a *fixed* multiplier `L_μ` suffices. -/
theorem floor_nonneg (q a b t : ℕ) (hq : 2 ≤ q) (hqt : 2 * t - 1 ≤ q) :
    a / q + b / q + (a + t) / q + (b + t) / q
      ≤ (a + b + 1) / q + (a + b + t) / q + (t - 1) / q := by
  have hq0 : 0 < q := by omega
  have htq : t < q := by omega
  have hr : a % q < q := Nat.mod_lt _ hq0
  have hs : b % q < q := Nat.mod_lt _ hq0
  have e1 : (a + t) / q = a / q + (a % q + t) / q := shift_div q a t hq0
  have e2 : (b + t) / q = b / q + (b % q + t) / q := shift_div q b t hq0
  have e3 : (a + b + 1) / q = a / q + b / q + (a % q + b % q + 1) / q := reduce_ab q a b 1 hq0
  have e4 : (a + b + t) / q = a / q + b / q + (a % q + b % q + t) / q := reduce_ab q a b t hq0
  have hz : (t - 1) / q = 0 := Nat.div_eq_of_lt (by omega)
  have key := floor_key_nonneg q (a % q) (b % q) t hq hqt hr hs htq
  have n1 : 0 ≤ (a % q + t) / q := Nat.zero_le _
  have n2 : 0 ≤ (b % q + t) / q := Nat.zero_le _
  have n3 : 0 ≤ (a % q + b % q + 1) / q := Nat.zero_le _
  have n4 : 0 ≤ (a % q + b % q + t) / q := Nat.zero_le _
  rw [e1, e2, e3, e4, hz]
  omega

/-! ## Legendre: what the floor statements are FOR

A floor bound that nothing consumes proves nothing about the conjecture. These three
declarations are the consumer: they turn the termwise bounds into a statement about the
`p`-adic valuation of the factorial ratio, which is what integrality is about. -/

/-- The two floor statements packaged as the single **termwise** bound Legendre's formula sums:
the denominator's `i`-th term exceeds the numerator's by at most one, and by nothing at all once
`p^i ≥ 2t−1`. -/
theorem legendre_term (p i a b t : ℕ) (hp : 2 ≤ p) (hi : 1 ≤ i) :
    a / p ^ i + b / p ^ i + (a + t) / p ^ i + (b + t) / p ^ i
      ≤ (t - 1) / p ^ i + (a + b + 1) / p ^ i + (a + b + t) / p ^ i
        + (if p ^ i < 2 * t - 1 then 1 else 0) := by
  have hq : 2 ≤ p ^ i := by
    calc 2 ≤ p := hp
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ i := Nat.pow_le_pow_right (by omega) hi
  by_cases h : p ^ i < 2 * t - 1
  · rw [if_pos h]
    have := floor_ge_neg_one (p ^ i) a b t hq
    omega
  · rw [if_neg h]
    have := floor_nonneg (p ^ i) a b t hq (by omega)
    omega

/-- **Summed over prime powers.** The total excess of the denominator over the numerator is at
most the number of `i` with `p^i < 2t−1` — a count depending on `t` alone, which is exactly why a
*fixed* multiplier clears every denominator at once. -/
theorem legendre_sum_bound (p a b t bnd : ℕ) (hp : 2 ≤ p) :
    ∑ i ∈ Finset.Ico 1 bnd, (a / p ^ i + b / p ^ i + (a + t) / p ^ i + (b + t) / p ^ i)
      ≤ ∑ i ∈ Finset.Ico 1 bnd,
            ((t - 1) / p ^ i + (a + b + 1) / p ^ i + (a + b + t) / p ^ i)
          + ((Finset.Ico 1 bnd).filter (fun i => p ^ i < 2 * t - 1)).card := by
  rw [Finset.card_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum ?_
  intro i hi
  exact legendre_term p i a b t hp (Finset.mem_Ico.1 hi).1

/-- `p`-adic valuation of a product of four nonzero naturals. -/
theorem factorization_mul4 (p x y z w : ℕ) (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) (hw : w ≠ 0) :
    (x * y * z * w).factorization p
      = x.factorization p + y.factorization p + z.factorization p + w.factorization p := by
  rw [Nat.factorization_mul (Nat.mul_ne_zero (Nat.mul_ne_zero hx hy) hz) hw,
    Nat.factorization_mul (Nat.mul_ne_zero hx hy) hz, Nat.factorization_mul hx hy]
  simp

/-- `p`-adic valuation of a product of three nonzero naturals. -/
theorem factorization_mul3 (p x y z : ℕ) (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    (x * y * z).factorization p
      = x.factorization p + y.factorization p + z.factorization p := by
  rw [Nat.factorization_mul (Nat.mul_ne_zero hx hy) hz, Nat.factorization_mul hx hy]
  simp

/-- **THE CONSUMING STATEMENT.** For every prime `p`, the denominator `a! b! (a+t)! (b+t)!` of the
factorial form of `2 C_μ(n,k)` carries at most `#{i : p^i < 2t−1}` more factors of `p` than the
numerator `(t−1)! (a+b+1)! (a+b+t)!`. The floor lemmas are exactly what proves this, and this is
exactly what a fixed multiplier has to beat. -/
theorem factorization_bound (p a b t bnd : ℕ) (hp : p.Prime) (ht : 1 ≤ t)
    (hbnd : Nat.log p (a + b + t) < bnd) :
    (Nat.factorial a * Nat.factorial b * Nat.factorial (a + t)
        * Nat.factorial (b + t)).factorization p
      ≤ (Nat.factorial (t - 1) * Nat.factorial (a + b + 1)
          * Nat.factorial (a + b + t)).factorization p
        + ((Finset.Ico 1 bnd).filter (fun i => p ^ i < 2 * t - 1)).card := by
  have F : ∀ n : ℕ, n ≤ a + b + t →
      (Nat.factorial n).factorization p = ∑ i ∈ Finset.Ico 1 bnd, n / p ^ i := fun n hn =>
    Nat.factorization_factorial hp (lt_of_le_of_lt (Nat.log_mono_right hn) hbnd)
  rw [factorization_mul4 p _ _ _ _ (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)
      (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _),
    factorization_mul3 p _ _ _ (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)
      (Nat.factorial_ne_zero _),
    F a (by omega), F b (by omega), F (a + t) (by omega), F (b + t) (by omega),
    F (t - 1) (by omega), F (a + b + 1) (by omega), F (a + b + t) (by omega),
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact legendre_sum_bound p a b t bnd hp.two_le

end Principia.MathDB.P322992
