import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.List.GetD
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false

/-!
# MathDB #323296 — Guo–Zeng Conjecture 4.1 is FALSE

Write-up: `mathdb-open-problems/problems/323296/solution.tex`, collaborator branch
`mathdb-results` of `antoshashakov/Principia-Math-In-Progress` (enrolled here 2026-09-28 from the
third hundred, see `THIRD100-ENROLMENT.md`).
Source: V. J. W. Guo and J. Zeng, *On Zudilin's q-question about Schmidt's problem*, Electron. J.
Combin. **19**(3) (2012) P4 (arXiv:1204.0187v3), **Conjecture 4.1**: for every `s > 1` and `N ≥ 0`
some integer `r > s` makes `c₀^{(r,s)}, …, c_N^{(r,s)}` all integers.

With `B(n,k) = C(n,k)·C(n+k,k)` and `Fₙ(r) = ∑ₖ B(n,k)^r`, the coefficients `c_k^{(r,s)}` are
determined by `Fₙ(r) = ∑ₖ B(n,k)^s c_k^{(r,s)}`. **The counterexample is `s = 2`, `N = 14`.**

## The coefficients are never constructed, and that is deliberate

`IsCoeffSeq r c` says only that `c` *satisfies the defining relations*. Nothing here solves the
triangular system or defines `c` by recursion, because the conjecture asks about the coefficients
and any `c` satisfying the relations **is** them: the diagonal `B(n,n)^2` is nonzero, so forward
substitution determines `c` uniquely (`coeffSeq_unique` records this). Refuting existence over all
such `c` is therefore exactly the conjecture's negation, and it is strictly stronger than refuting
it for one construction.

## Why `decide` can carry the whole certificate, and why `native_decide` is not an option

Every finite fact below is a `decide` over a `Finset` range, and the campaign's gate **refuses
`ofReduceBool`**, so `native_decide` would disqualify the row outright. That made the arithmetic
sizes the deciding question, and they were measured before any Lean was written
(`verify_323296.py` prints them): the largest `B(n,k)` for `n ≤ 14` is `1963217256`, the largest
kernel column sum is `4004697694323907152`, and `b^17` never exceeds 157 digits. All of it reduces
in seconds. Note the count that made this cheap: **only 40 of the 120 pairs `(n,k)` have `3 ∤
B(n,k)`**
(64 and 72 for the two vectors at 19), so the unit-part sums are much smaller than the full ones.

## The shape of the refutation

1. **`necessary_v` / `necessary_u` / `necessary_w`** — if `c₀ … c_d` are integers then
   `m ∣ ∑ₙ zₙ Fₙ(r)`, because `∑ₙ zₙ Fₙ(r) = ∑ₖ cₖ (∑ₙ zₙ B(n,k)²)` and each **kernel column** is
   divisible by `m`. The sum swap is `Finset.sum_comm`, and it is legitimate on the full square
   because `B(n,k) = 0` for `k > n` (`Bc_eq_zero_of_lt`).
2. **`kernel_v` / `kernel_u` / `kernel_w`** — the 38 column divisibilities, three `decide`s
   quantified over `k`, not 38 separate theorems.
3. **`unit_part_v`** — for `r ≥ 6` every term with `3 ∣ B(n,k)` vanishes mod `729`, since
   `3 ∣ b → 3^6 ∣ b^6 ∣ b^r`. So the condition is on the **unit part** `U_{v,3}(r)` alone. Likewise
   at `19` for `r ≥ 2`.
4. **`period_18`** — `U_{v,3}(h+18t) ≡ U_{v,3}(h) (mod 729)`. This is the only piece of general
   mathematics: `b^18 = 1 + 27q` for a unit `b`, so `b^{18t} ≡ 1 + 27tq (mod 729)` by
   `one_add_mul_pow_mod_sq`, and the resulting `27t·∑ zₙ q(b) b^h` vanishes because the inner sum is
   itself divisible by `27` (`deriv_v`, the write-up's 18 identities).
5. **`table_v`** — `U_{v,3}(h) ≡ 81·τ(h) (mod 729)` with `τ` the write-up's table, which is zero
   exactly at `h = 5, 14`. Hence `r ≡ 5` or `14 (mod 18)`.
6. **At `19`** the same machinery makes `U/19` affine in `t`, and the two vectors demand
   incompatible `t (mod 19)` — `8` against `9` for `h = 5`, `1` against `15` for `h = 14`.
7. **`r = 3, 4, 5`** are excluded by exact fractions: the first four relations force
   `c₃ = 343/5`, `11612/5`, `342076/5`, none an integer.

## 215 check

* **The three exceptional exponents are not an afterthought but the reason the theorem reads
  `r > 2` rather than `r ≥ 6`.** They are checked here from the defining relations, not quoted.
* **A congruence checked against nothing can be vacuously true**, so the verifier's positive control
  is the three fractions rather than any of the congruences, and it also confirms the condition at
  `3` alone *is* satisfiable (first `r ≥ 6` passing it is `14`) — so the mod-3 step genuinely
  narrows rather than closing the argument by itself.
* A brute-force cross-check over `r ∈ [6, 201)` finds no `r` satisfying all three congruences,
  agreeing with the algebraic argument on that range.
-/

namespace Principia.MathDB.P323296

open Finset

/-! ### The Schmidt-type numbers -/

/-- `B(n,k) = C(n,k)·C(n+k,k)`, which is `0` when `k > n`. -/
def Bc (n k : ℕ) : ℕ := Nat.choose n k * Nat.choose (n + k) k

theorem Bc_eq_zero_of_lt {n k : ℕ} (h : n < k) : Bc n k = 0 := by
  simp [Bc, Nat.choose_eq_zero_of_lt h]

theorem Bc_diag_pos (n : ℕ) : 0 < Bc n n := by
  have h1 : 0 < Nat.choose n n := by simp
  have h2 : 0 < Nat.choose (n + n) n := Nat.choose_pos (by omega)
  exact Nat.mul_pos h1 h2

/-- The ten values the small-exponent argument needs, as numerals. -/
theorem Bc_small : Bc 0 0 = 1 ∧ Bc 1 0 = 1 ∧ Bc 1 1 = 2 ∧ Bc 2 0 = 1 ∧ Bc 2 1 = 6 ∧
    Bc 2 2 = 6 ∧ Bc 3 0 = 1 ∧ Bc 3 1 = 12 ∧ Bc 3 2 = 30 ∧ Bc 3 3 = 20 := by decide

/-- `Fₙ(r) = ∑_{k ≤ n} B(n,k)^r`. -/
def Fn (n r : ℕ) : ℤ := ∑ k ∈ range (n + 1), (Bc n k : ℤ) ^ r

theorem Fn_zero (r : ℕ) : Fn 0 r = 1 := by
  simp [Fn, Bc]

theorem Fn_one (r : ℕ) : Fn 1 r = 1 + 2 ^ r := by
  obtain ⟨_, h10, h11, -⟩ := Bc_small
  simp [Fn, Finset.sum_range_succ, h10, h11]

theorem Fn_two (r : ℕ) : Fn 2 r = 1 + 2 * 6 ^ r := by
  obtain ⟨-, -, -, h20, h21, h22, -⟩ := Bc_small
  simp [Fn, Finset.sum_range_succ, h20, h21, h22]
  ring

theorem Fn_three (r : ℕ) : Fn 3 r = 1 + 12 ^ r + 30 ^ r + 20 ^ r := by
  obtain ⟨-, -, -, -, -, -, h30, h31, h32, h33⟩ := Bc_small
  simp [Fn, Finset.sum_range_succ, h30, h31, h32, h33]

/-- `c` satisfies the relations that define the Guo–Zeng coefficients at `s = 2`. -/
def IsCoeffSeq (r : ℕ) (c : ℕ → ℚ) : Prop :=
  ∀ n, ((Fn n r : ℤ) : ℚ) = ∑ k ∈ range (n + 1), ((Bc n k : ℚ)) ^ 2 * c k

/-- The relations determine `c` uniquely, because the diagonal is nonzero. This is why refuting
*existence* is the conjecture's negation rather than a weaker statement about one construction. -/
theorem coeffSeq_unique {r : ℕ} {c d : ℕ → ℚ} (hc : IsCoeffSeq r c) (hd : IsCoeffSeq r d) :
    ∀ n, c n = d n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have h := (hc n).symm.trans (hd n)
    rw [Finset.sum_range_succ, Finset.sum_range_succ] at h
    have hagree : ∑ k ∈ range n, ((Bc n k : ℚ)) ^ 2 * c k
        = ∑ k ∈ range n, ((Bc n k : ℚ)) ^ 2 * d k :=
      Finset.sum_congr rfl fun k hk => by rw [ih k (Finset.mem_range.mp hk)]
    rw [hagree] at h
    have hdiag : ((Bc n n : ℚ)) ^ 2 ≠ 0 := by
      have h0 : (0 : ℚ) < (Bc n n : ℚ) := by
        exact_mod_cast Nat.cast_pos.mpr (Bc_diag_pos n)
      positivity
    exact mul_left_cancel₀ hdiag (by linarith)

/-! ### The three modular left-kernel vectors -/

def Vl : List ℤ := [54, 0, 189, 84, 0, 564, 414, 243, 153, 333, 486, 315, 80, 0, 1]
def Ul : List ℤ := [171, 133, 19, 190, 266, 95, 76, 76, 56, 0, 1]
def Wl : List ℤ := [342, 247, 342, 171, 266, 38, 190, 75, 213, 0, 281, 1]

def Vv (n : ℕ) : ℤ := Vl.getD n 0
def Uv (n : ℕ) : ℤ := Ul.getD n 0
def Wv (n : ℕ) : ℤ := Wl.getD n 0

/-- **`v A₁₄ ≡ 0 (mod 729)`** — fifteen column divisibilities in one `decide`. -/
theorem kernel_v : ∀ k < 15, (729 : ℤ) ∣ ∑ n ∈ range 15, Vv n * (Bc n k : ℤ) ^ 2 := by decide

/-- **`u A₁₀ ≡ 0 (mod 361)`**. -/
theorem kernel_u : ∀ k < 11, (361 : ℤ) ∣ ∑ n ∈ range 11, Uv n * (Bc n k : ℤ) ^ 2 := by decide

/-- **`w A₁₁ ≡ 0 (mod 361)`**. -/
theorem kernel_w : ∀ k < 12, (361 : ℤ) ∣ ∑ n ∈ range 12, Wv n * (Bc n k : ℤ) ^ 2 := by decide

/-! ### From integrality to a congruence

`∑ₙ zₙ Fₙ(r) = ∑ₖ (∑ₙ zₙ B(n,k)²) cₖ`, and every column on the right is divisible by the modulus.
The swap is legitimate over the full square because `B(n,k) = 0` above the diagonal, so widening
each inner range from `n+1` to `d+1` adds only zeros. -/

/-- Widening the inner range adds only zeros, since `B(n,k) = 0` for `k > n`. -/
theorem sum_widen {d n : ℕ} (hn : n ≤ d) (f : ℕ → ℚ) (hf : ∀ k, Bc n k = 0 → f k = 0) :
    ∑ k ∈ range (n + 1), f k = ∑ k ∈ range (d + 1), f k := by
  refine Finset.sum_subset (fun k hk => Finset.mem_range.mpr ?_) ?_
  · have hk' : k < n + 1 := Finset.mem_range.mp hk
    omega
  · intro k _ hk
    have hnk : n < k := by
      by_contra hcon
      exact hk (Finset.mem_range.mpr (by omega))
    exact hf k (Bc_eq_zero_of_lt hnk)

/-- **THE BRIDGE.** If `c₀ … c_d` are integers and every kernel column is divisible by `m`, then so
is `∑ₙ zₙ Fₙ(r)`. This is what the kernel certificates are for. -/
theorem necessary {d : ℕ} {m : ℤ} {z : ℕ → ℤ} {r : ℕ} {c : ℕ → ℚ}
    (hc : IsCoeffSeq r c) (w : ℕ → ℤ) (hw : ∀ k ≤ d, c k = (w k : ℚ))
    (hker : ∀ k, k < d + 1 → m ∣ ∑ n ∈ range (d + 1), z n * (Bc n k : ℤ) ^ 2) :
    m ∣ ∑ n ∈ range (d + 1), z n * Fn n r := by
  have hid : ∑ n ∈ range (d + 1), z n * Fn n r
      = ∑ k ∈ range (d + 1), (∑ n ∈ range (d + 1), z n * (Bc n k : ℤ) ^ 2) * w k := by
    have hQ : ((∑ n ∈ range (d + 1), z n * Fn n r : ℤ) : ℚ)
        = ((∑ k ∈ range (d + 1), (∑ n ∈ range (d + 1), z n * (Bc n k : ℤ) ^ 2) * w k : ℤ) : ℚ) := by
      push_cast
      calc ∑ n ∈ range (d + 1), (z n : ℚ) * ((Fn n r : ℤ) : ℚ)
          = ∑ n ∈ range (d + 1), (z n : ℚ) *
              ∑ k ∈ range (d + 1), ((Bc n k : ℚ)) ^ 2 * c k := by
            refine Finset.sum_congr rfl fun n hn => ?_
            rw [hc n]
            congr 1
            refine sum_widen (d := d) ?_ _ (fun k hk => by rw [hk]; push_cast; ring)
            have := Finset.mem_range.mp hn
            omega
        _ = ∑ n ∈ range (d + 1), ∑ k ∈ range (d + 1),
              (z n : ℚ) * (((Bc n k : ℚ)) ^ 2 * c k) :=
            Finset.sum_congr rfl fun n _ => mul_sum _ _ _
        _ = ∑ k ∈ range (d + 1), ∑ n ∈ range (d + 1),
              (z n : ℚ) * (((Bc n k : ℚ)) ^ 2 * c k) := Finset.sum_comm
        _ = ∑ k ∈ range (d + 1),
              (∑ n ∈ range (d + 1), (z n : ℚ) * ((Bc n k : ℚ)) ^ 2) * (w k : ℚ) := by
            refine Finset.sum_congr rfl fun k hk => ?_
            rw [sum_mul, ← hw k (by have := Finset.mem_range.mp hk; omega)]
            exact Finset.sum_congr rfl fun n _ => by ring
    exact Int.cast_injective hQ
  rw [hid]
  exact dvd_sum fun k hk => Dvd.dvd.mul_right (hker k (Finset.mem_range.mp hk)) _

/-! ### The three exceptional exponents `r = 3, 4, 5`

These are the reason the theorem reads `r > 2` rather than `r ≥ 6`, and they are derived here from
the defining relations rather than quoted. The first four relations force `c₃`, whose denominator
is `5`. -/

/-- A rational `x` with `5·x = a` and `5 ∤ a` is not an integer. -/
theorem not_int_of_five_mul {x : ℚ} {a : ℤ} (hx : (5 : ℚ) * x = (a : ℚ))
    (ha : ¬ (5 : ℤ) ∣ a) : ¬ ∃ z : ℤ, x = (z : ℚ) := by
  rintro ⟨z, rfl⟩
  have hcast : ((5 * z : ℤ) : ℚ) = ((a : ℤ) : ℚ) := by push_cast; linarith
  exact ha ⟨z, (Int.cast_injective hcast).symm⟩

/-- The four relations, with every `B` replaced by its numeral. -/
theorem four_relations {r : ℕ} {c : ℕ → ℚ} (hc : IsCoeffSeq r c) :
    c 0 = 1 ∧ (1 + 2 ^ r : ℚ) = c 0 + 4 * c 1 ∧
      (1 + 2 * 6 ^ r : ℚ) = c 0 + 36 * c 1 + 36 * c 2 ∧
      (1 + 12 ^ r + 30 ^ r + 20 ^ r : ℚ) = c 0 + 144 * c 1 + 900 * c 2 + 400 * c 3 := by
  obtain ⟨h00, h10, h11, h20, h21, h22, h30, h31, h32, h33⟩ := Bc_small
  have e0 := hc 0
  have e1 := hc 1
  have e2 := hc 2
  have e3 := hc 3
  rw [Fn_zero] at e0
  rw [Fn_one] at e1
  rw [Fn_two] at e2
  rw [Fn_three] at e3
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, h00, h10, h11, h20, h21, h22,
    h30, h31, h32, h33] at e0 e1 e2 e3
  push_cast at e0 e1 e2 e3
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- **`c₃` is pinned by the four relations.** The intermediate values are `c₀ = 1`,
`c₁ = 2ʳ/4`, `c₂ = (2·6ʳ − 9·2ʳ)/36`. (A first attempt wrote `c₁ = (2ʳ−1)/4`, which `linarith`
refused; the relation gives `4c₁ = 2ʳ` because `c₀ = 1` already absorbs the constant term.) -/
theorem four_hundred_mul_c3 {r : ℕ} {c : ℕ → ℚ} (hc : IsCoeffSeq r c) :
    (400 : ℚ) * c 3 = (12 : ℚ) ^ r + 30 ^ r + 20 ^ r - 50 * 6 ^ r + 189 * 2 ^ r := by
  obtain ⟨g0, g1, g2, g3⟩ := four_relations hc
  rw [g0] at g1 g2 g3
  have hc1 : c 1 = (2 : ℚ) ^ r / 4 := by linarith
  rw [hc1] at g2 g3
  have hc2 : c 2 = (2 * (6 : ℚ) ^ r - 9 * 2 ^ r) / 36 := by linarith
  rw [hc2] at g3
  linarith

/-- **`r = 3` is excluded**: `c₃ = 343/5`. -/
theorem not_int_three {c : ℕ → ℚ} (hc : IsCoeffSeq 3 c) : ¬ ∃ z : ℤ, c 3 = (z : ℚ) := by
  have h := four_hundred_mul_c3 hc
  norm_num at h
  refine not_int_of_five_mul (a := 343) ?_ (by decide)
  push_cast
  linarith

/-- **`r = 4` is excluded**: `c₃ = 11612/5`. -/
theorem not_int_four {c : ℕ → ℚ} (hc : IsCoeffSeq 4 c) : ¬ ∃ z : ℤ, c 3 = (z : ℚ) := by
  have h := four_hundred_mul_c3 hc
  norm_num at h
  refine not_int_of_five_mul (a := 11612) ?_ (by decide)
  push_cast
  linarith

/-- **`r = 5` is excluded**: `c₃ = 342076/5`. -/
theorem not_int_five {c : ℕ → ℚ} (hc : IsCoeffSeq 5 c) : ¬ ∃ z : ℤ, c 3 = (z : ℚ) := by
  have h := four_hundred_mul_c3 hc
  norm_num at h
  refine not_int_of_five_mul (a := 342076) ?_ (by decide)
  push_cast
  linarith

/-- **CONJECTURE 4.1 FAILS AT `r = 3, 4, 5`** — three of the infinitely many candidate exponents
refuted outright, with no congruence machinery involved. -/
theorem conjecture_4_1_false_small (r : ℕ) (hr : r = 3 ∨ r = 4 ∨ r = 5) :
    ¬ ∃ c : ℕ → ℚ, IsCoeffSeq r c ∧ ∀ k ≤ 14, ∃ z : ℤ, c k = (z : ℚ) := by
  rintro ⟨c, hc, hint⟩
  rcases hr with rfl | rfl | rfl
  · exact not_int_three hc (hint 3 (by norm_num))
  · exact not_int_four hc (hint 3 (by norm_num))
  · exact not_int_five hc (hint 3 (by norm_num))

/-! ## The `r ≥ 6` half

The residue recorded when this row was first banked. Nothing here needs theory Mathlib lacks; the
whole of it is finite certificates plus one general lemma about `(1 + m x)^t`. -/

/-- The **unit part** of `∑ₙ zₙ Fₙ(a)`: the terms whose `B(n,k)` is prime to `p`. The guard also
disposes of `k > n` for free, since `B(n,k) = 0` there and `p ∣ 0`. -/
def Usum (z : ℕ → ℤ) (d p a : ℕ) : ℤ :=
  ∑ n ∈ range (d + 1), ∑ k ∈ range (d + 1),
    if Bc n k % p = 0 then 0 else z n * (Bc n k : ℤ) ^ a

/-- The **`t`-slope**: what the linear term of the expansion contributes. -/
def Dsum (z : ℕ → ℤ) (d p a : ℕ) (m : ℤ) : ℤ :=
  ∑ n ∈ range (d + 1), ∑ k ∈ range (d + 1),
    if Bc n k % p = 0 then 0 else z n * (((Bc n k : ℤ) ^ 18 - 1) / m) * (Bc n k : ℤ) ^ a

/-- `Fₙ(r)` over the widened range, for `n ≤ d`. -/
theorem Fn_widen {d n : ℕ} (hn : n ≤ d) {r : ℕ} (hr : 0 < r) :
    Fn n r = ∑ k ∈ range (d + 1), (Bc n k : ℤ) ^ r := by
  rw [Fn]
  refine Finset.sum_subset (fun k hk => Finset.mem_range.mpr ?_) ?_
  · have hk' : k < n + 1 := Finset.mem_range.mp hk
    omega
  · intro k _ hk
    have hnk : n < k := by
      by_contra hcon
      exact hk (Finset.mem_range.mpr (by omega))
    rw [Bc_eq_zero_of_lt hnk]
    simp [hr.ne']

/-- **THE ONE PIECE OF GENERAL MATHEMATICS.** `(1 + m x)^t ≡ 1 + m t x (mod m²)`. -/
theorem one_add_mul_pow_mod_sq (m x : ℤ) (t : ℕ) :
    (m ^ 2 : ℤ) ∣ (1 + m * x) ^ t - (1 + m * (t : ℤ) * x) := by
  induction t with
  | zero => simp
  | succ t ih =>
    obtain ⟨c, hc⟩ := ih
    have hA : (1 + m * x) ^ t = 1 + m * (t : ℤ) * x + m ^ 2 * c := by linarith
    refine ⟨c + (t : ℤ) * x ^ 2 + m * c * x, ?_⟩
    push_cast
    rw [pow_succ, hA]
    ring

/-- Dropping the non-unit terms costs a multiple of `p^e`, because `p ∣ B` gives `p^e ∣ B^r`. -/
theorem sub_Usum_dvd {d p e : ℕ} (z : ℕ → ℤ) {r : ℕ} (he : e ≤ r) (hr : 0 < r) :
    ((p : ℤ) ^ e) ∣ (∑ n ∈ range (d + 1), z n * Fn n r) - Usum z d p r := by
  have hsplit : (∑ n ∈ range (d + 1), z n * Fn n r) - Usum z d p r
      = ∑ n ∈ range (d + 1), ∑ k ∈ range (d + 1),
          (if Bc n k % p = 0 then z n * (Bc n k : ℤ) ^ r else 0) := by
    simp only [Usum]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [Fn_widen (d := d) (by have := Finset.mem_range.mp hn; omega) hr, Finset.mul_sum,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hg : Bc n k % p = 0 <;> simp [hg]
  rw [hsplit]
  refine Finset.dvd_sum fun n _ => Finset.dvd_sum fun k _ => ?_
  by_cases hg : Bc n k % p = 0
  · simp only [hg, if_true]
    have hpb : (p : ℤ) ∣ (Bc n k : ℤ) := by
      exact Int.natCast_dvd_natCast.mpr (Nat.dvd_of_mod_eq_zero hg)
    exact Dvd.dvd.mul_left (dvd_trans (pow_dvd_pow _ he) (pow_dvd_pow_of_dvd hpb r)) _
  · simp [hg]

/-- **THE PERIODICITY.** `Usum` at `h + 18t` differs from `Usum` at `h` by `m·t·Dsum`, modulo `m²`.
Every unit `b` satisfies `b^18 = 1 + m·q`, so `b^{18t} ≡ 1 + m t q (mod m²)`. -/
theorem Usum_period {d p : ℕ} {m : ℤ} (hm : m ≠ 0) (z : ℕ → ℤ) (h t : ℕ)
    (heu : ∀ n < d + 1, ∀ k < d + 1, Bc n k % p ≠ 0 → m ∣ (Bc n k : ℤ) ^ 18 - 1) :
    (m ^ 2) ∣ Usum z d p (h + 18 * t) - Usum z d p h - m * (t : ℤ) * Dsum z d p h m := by
  have key : Usum z d p (h + 18 * t) - Usum z d p h - m * (t : ℤ) * Dsum z d p h m
      = ∑ n ∈ range (d + 1), ∑ k ∈ range (d + 1),
          (if Bc n k % p = 0 then 0 else
            z n * (Bc n k : ℤ) ^ (h + 18 * t) - z n * (Bc n k : ℤ) ^ h
              - m * (t : ℤ) * (z n * (((Bc n k : ℤ) ^ 18 - 1) / m) * (Bc n k : ℤ) ^ h)) := by
    simp only [Usum, Dsum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun k _ => ?_
    by_cases hg : Bc n k % p = 0 <;> simp [hg]
  rw [key]
  refine Finset.dvd_sum fun n _ => Finset.dvd_sum fun k _ => ?_
  by_cases hg : Bc n k % p = 0
  · simp [hg]
  · simp only [hg, if_false]
    obtain ⟨q, hq⟩ := heu n (Finset.mem_range.mp ‹n ∈ range (d+1)›) k (Finset.mem_range.mp ‹k ∈
    range (d+1)›) hg
    set b : ℤ := (Bc n k : ℤ) with hb
    have hq' : b ^ 18 = 1 + m * q := by linarith [hq]
    have hdiv : ((b ^ 18 - 1) / m) = q := by
      rw [hq', show 1 + m * q - 1 = m * q by ring, Int.mul_ediv_cancel_left _ hm]
    obtain ⟨cc, hcc⟩ := one_add_mul_pow_mod_sq m q t
    have hpow : b ^ (h + 18 * t) = b ^ h * (1 + m * q) ^ t := by
      rw [pow_add, pow_mul, hq']
    refine ⟨z n * b ^ h * cc, ?_⟩
    rw [hdiv, hpow]
    have hc' : (1 + m * q) ^ t = 1 + m * (t : ℤ) * q + m ^ 2 * cc := by linarith [hcc]
    rw [hc']
    ring

/-! ### The finite certificates at `3` and at `19` -/

/-- Euler at `27`: every `B(n,k)` prime to `3` has `b^18 ≡ 1 (mod 27)`. Bounded, so `decide`. -/
theorem euler_three : ∀ n < 15, ∀ k < 15, Bc n k % 3 ≠ 0 → (27 : ℤ) ∣ (Bc n k : ℤ) ^ 18 - 1 := by
  decide

/-- Fermat at `19`. -/
theorem fermat_nineteen :
    ∀ n < 15, ∀ k < 15, Bc n k % 19 ≠ 0 → (19 : ℤ) ∣ (Bc n k : ℤ) ^ 18 - 1 := by decide

/-- The write-up's table: `U_{v,3}(h) ≡ 81·τ(h) (mod 729)`. -/
def tau : ℕ → ℤ := fun h => ([4, 2, 6, 4, 2, 0, 1, 8, 3, 1, 8, 6, 7, 5, 0, 7, 5, 3] : List
ℤ).getD h 0

theorem table_v : ∀ h < 18, (729 : ℤ) ∣ Usum Vv 14 3 h - 81 * tau h := by decide

/-- The write-up's 18 derivative identities. -/
theorem deriv_v : ∀ h < 18, (27 : ℤ) ∣ Dsum Vv 14 3 h 27 := by decide

/-- `τ` vanishes exactly at `h = 5` and `h = 14`. -/
theorem tau_eq_zero_iff : ∀ h < 18, (tau h = 0 ↔ h = 5 ∨ h = 14) := by decide

theorem tau_lt_nine : ∀ h < 18, tau h < 9 ∧ 0 ≤ tau h := by decide

/-- The four values at `19`: `U/19 ≡ a` and the slope `≡ b`. -/
theorem table_u : (361 : ℤ) ∣ Usum Uv 10 19 5 - 19 * 3 ∧ (361 : ℤ) ∣ Usum Uv 10 19 14 - 19 * 9 := by
  decide

theorem table_w : (361 : ℤ) ∣ Usum Wv 11 19 5 - 19 * 7 ∧ (361 : ℤ) ∣ Usum Wv 11 19 14 - 19 * 1 := by
  decide

theorem deriv_u : (19 : ℤ) ∣ Dsum Uv 10 19 5 19 - 2 ∧ (19 : ℤ) ∣ Dsum Uv 10 19 14 19 - 10 := by
  decide

theorem deriv_w : (19 : ℤ) ∣ Dsum Wv 11 19 5 19 - 14 ∧ (19 : ℤ) ∣ Dsum Wv 11 19 14 19 - 5 := by
  decide

/-! ### Assembling the `r ≥ 6` contradiction -/

/-- The condition the kernel vector `z` imposes on the unit part, for `r ≥ e`. -/
theorem unit_condition {d e : ℕ} {p : ℕ} {z : ℕ → ℤ} {r : ℕ} (he : e ≤ r) (hr : 0 < r)
    (hdvd : ((p : ℤ) ^ e) ∣ ∑ n ∈ range (d + 1), z n * Fn n r) :
    ((p : ℤ) ^ e) ∣ Usum z d p r := by
  have h := sub_Usum_dvd (d := d) (p := p) (e := e) z he hr
  have : Usum z d p r = (∑ n ∈ range (d + 1), z n * Fn n r)
      - ((∑ n ∈ range (d + 1), z n * Fn n r) - Usum z d p r) := by ring
  rw [this]
  exact dvd_sub hdvd h

/-- With the period and the slope identity, the condition at `3` depends only on `r % 18`. -/
theorem three_condition_mod {t h : ℕ} (hh : h < 18)
    (hdvd : (729 : ℤ) ∣ Usum Vv 14 3 (h + 18 * t)) : (729 : ℤ) ∣ Usum Vv 14 3 h := by
  have hper := Usum_period (d := 14) (p := 3) (m := 27) (by norm_num) Vv h t
    (fun n hn k hk hg => euler_three n hn k hk hg)
  have hslope : (729 : ℤ) ∣ 27 * (t : ℤ) * Dsum Vv 14 3 h 27 := by
    obtain ⟨cc, hcc⟩ := deriv_v h hh
    exact ⟨(t : ℤ) * cc, by rw [hcc]; ring⟩
  have hsq : ((27 : ℤ) ^ 2) = 729 := by norm_num
  rw [hsq] at hper
  have := dvd_sub hdvd hper
  have heq : Usum Vv 14 3 (h + 18 * t)
      - (Usum Vv 14 3 (h + 18 * t) - Usum Vv 14 3 h - 27 * (t : ℤ) * Dsum Vv 14 3 h 27)
      = Usum Vv 14 3 h + 27 * (t : ℤ) * Dsum Vv 14 3 h 27 := by ring
  rw [heq] at this
  have : (729 : ℤ) ∣ Usum Vv 14 3 h + 27 * (t : ℤ) * Dsum Vv 14 3 h 27 -
      27 * (t : ℤ) * Dsum Vv 14 3 h 27 := dvd_sub this hslope
  simpa using this

/-- **The condition at `3` forces `r ≡ 5` or `14 (mod 18)`.** -/
theorem r_mod_eighteen {r : ℕ} (hdvd : (729 : ℤ) ∣ Usum Vv 14 3 r) : r % 18 = 5 ∨ r % 18 = 14 := by
  have hh : r % 18 < 18 := Nat.mod_lt _ (by norm_num)
  have hre : r = r % 18 + 18 * (r / 18) := by omega
  rw [hre] at hdvd
  have h0 := three_condition_mod hh hdvd
  obtain ⟨cc, hcc⟩ := table_v (r % 18) hh
  have h81 : (729 : ℤ) ∣ 81 * tau (r % 18) := by
    have : (81 : ℤ) * tau (r % 18) = Usum Vv 14 3 (r % 18) - 729 * cc := by linarith
    rw [this]
    exact dvd_sub h0 ⟨cc, rfl⟩
  obtain ⟨e, he⟩ := h81
  have h9 : tau (r % 18) = 9 * e := by linarith
  obtain ⟨hlt, hge⟩ := tau_lt_nine (r % 18) hh
  have : tau (r % 18) = 0 := by
    rcases lt_trichotomy e 0 with h | h | h
    · exfalso; rw [h9] at hge; omega
    · rw [h9, h]; ring
    · exfalso; rw [h9] at hlt; omega
  exact (tau_eq_zero_iff (r % 18) hh).mp this

/-- With the period and slope at `19`, the condition becomes `19 ∣ a + t·b`. -/
theorem nineteen_condition {d : ℕ} {z : ℕ → ℤ} {a b : ℤ} {h t : ℕ}
    (heu : ∀ n < d + 1, ∀ k < d + 1, Bc n k % 19 ≠ 0 → (19 : ℤ) ∣ (Bc n k : ℤ) ^ 18 - 1)
    (htab : (361 : ℤ) ∣ Usum z d 19 h - 19 * a) (hsl : (19 : ℤ) ∣ Dsum z d 19 h 19 - b)
    (hdvd : (361 : ℤ) ∣ Usum z d 19 (h + 18 * t)) : (19 : ℤ) ∣ a + (t : ℤ) * b := by
  have hper := Usum_period (d := d) (p := 19) (m := 19) (by norm_num) z h t heu
  have hsq : ((19 : ℤ) ^ 2) = 361 := by norm_num
  rw [hsq] at hper
  obtain ⟨c1, hc1⟩ := hper
  obtain ⟨c2, hc2⟩ := htab
  obtain ⟨c3, hc3⟩ := hsl
  obtain ⟨c4, hc4⟩ := hdvd
  -- 361 * c4 = 19*a + 361*c2 + 19*t*(b + 19*c3) + 361*c1
  refine ⟨c4 - c2 - (t : ℤ) * c3 - c1, ?_⟩
  have e1 : Usum z d 19 (h + 18 * t) = Usum z d 19 h + 19 * (t : ℤ) * Dsum z d 19 h 19
      + 361 * c1 := by linarith
  rw [e1] at hc4
  have e2 : Usum z d 19 h = 19 * a + 361 * c2 := by linarith
  have e3 : Dsum z d 19 h 19 = b + 19 * c3 := by linarith
  rw [e2, e3] at hc4
  linarith

theorem heu19 : ∀ d : ℕ, d ≤ 14 →
    ∀ n < d + 1, ∀ k < d + 1, Bc n k % 19 ≠ 0 → (19 : ℤ) ∣ (Bc n k : ℤ) ^ 18 - 1 := by
  intro d hd n hn k hk hg
  exact fermat_nineteen n (by omega) k (by omega) hg

/-! ## The refutation, complete -/

/-- **GUO–ZENG CONJECTURE 4.1 IS FALSE.** For every `r > 2` some `cₖ` with `k ≤ 14` is not an
integer. `r = 3, 4, 5` go by exact fractions; every `r ≥ 6` is excluded because the condition at `3`
forces `r ≡ 5` or `14 (mod 18)` and the two vectors at `19` then demand incompatible `t (mod
19)`. -/
theorem conjecture_4_1_false (r : ℕ) (hr : 2 < r) :
    ¬ ∃ c : ℕ → ℚ, IsCoeffSeq r c ∧ ∀ k ≤ 14, ∃ z : ℤ, c k = (z : ℚ) := by
  rcases Nat.lt_or_ge r 6 with hsmall | hbig
  · exact conjecture_4_1_false_small r (by omega)
  rintro ⟨c, hc, hint⟩
  choose w hw using hint
  have hrpos : 0 < r := by omega
  -- the three necessary congruences
  have hv : (729 : ℤ) ∣ Usum Vv 14 3 r := by
    refine unit_condition (d := 14) (e := 6) (p := 3) (by omega) hrpos ?_
    have := necessary (d := 14) (m := (3 : ℤ) ^ 6) (z := Vv) hc
      (fun k => if hk : k ≤ 14 then w k hk else 0)
      (fun k hk => by rw [hw k hk]; simp [hk])
      (fun k hk => by simpa using kernel_v k hk)
    simpa using this
  have hu : (361 : ℤ) ∣ Usum Uv 10 19 r := by
    refine unit_condition (d := 10) (e := 2) (p := 19) (by omega) hrpos ?_
    have := necessary (d := 10) (m := (19 : ℤ) ^ 2) (z := Uv) hc
      (fun k => if hk : k ≤ 10 then w k (by omega) else 0)
      (fun k hk => by rw [hw k (by omega)]; simp [hk])
      (fun k hk => by simpa using kernel_u k hk)
    simpa using this
  have hwv : (361 : ℤ) ∣ Usum Wv 11 19 r := by
    refine unit_condition (d := 11) (e := 2) (p := 19) (by omega) hrpos ?_
    have := necessary (d := 11) (m := (19 : ℤ) ^ 2) (z := Wv) hc
      (fun k => if hk : k ≤ 11 then w k (by omega) else 0)
      (fun k hk => by rw [hw k (by omega)]; simp [hk])
      (fun k hk => by simpa using kernel_w k hk)
    simpa using this
  -- the condition at 3 pins the residue
  have hres := r_mod_eighteen hv
  have hre : r = r % 18 + 18 * (r / 18) := by omega
  set t := r / 18 with ht
  rcases hres with h5 | h14
  · rw [h5] at hre
    rw [hre] at hu hwv
    have cu := nineteen_condition (heu19 10 (by norm_num)) table_u.1 deriv_u.1 hu
    have cw := nineteen_condition (heu19 11 (by norm_num)) table_w.1 deriv_w.1 hwv
    -- 7*(3 + 2t) - (7 + 14t) = 14, and 19 does not divide 14
    obtain ⟨x, hx⟩ := cu
    obtain ⟨y, hy⟩ := cw
    have : (19 : ℤ) ∣ 14 := ⟨7 * x - y, by linarith⟩
    norm_num at this
  · rw [h14] at hre
    rw [hre] at hu hwv
    have cu := nineteen_condition (heu19 10 (by norm_num)) table_u.2 deriv_u.2 hu
    have cw := nineteen_condition (heu19 11 (by norm_num)) table_w.2 deriv_w.2 hwv
    -- (9 + 10t) - 2*(1 + 5t) = 7, and 19 does not divide 7
    obtain ⟨x, hx⟩ := cu
    obtain ⟨y, hy⟩ := cw
    have : (19 : ℤ) ∣ 7 := ⟨x - 2 * y, by linarith⟩
    norm_num at this

end Principia.MathDB.P323296
