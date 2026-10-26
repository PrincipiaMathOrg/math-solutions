import Mathlib

/-!
# MathDB #353583 — the factorial-partition sign conjecture is FALSE

Write-up `mathdb-open-problems/problems/353583/solution.tex`,
*An infinite counterexample to the factorial-partition sign conjecture*, 18 September 2026.

For a set `A` of positive integers let `c_A(ℓ,n)` count the unordered partitions of `n` into
exactly `ℓ` parts from `A`, and put `S_{A,k}(n) = ∑_{ℓ=0}^{n} (−1)^ℓ ℓ^k c_A(ℓ,n)`.  With
`U_m = {1!, …, m!}`, the second assertion of Gawron–Ulas Conjecture 4.4 predicts
`(−1)^n S_{U_m,k}(n) ≥ 0` for all sufficiently large `n` whenever `k ≥ m−1`.

It fails at `m = 3` (so `U_3 = {1,2,6}`) and `k = 2 = m−1`, along the arithmetic progression

`S_{{1,2,6},2}(12u+30) = −(u+3)(52u² + 147u + 35)/3 < 0`   for every `u ≥ 0`.

**Because the conjecture says "for all sufficiently large `n`", a single witness does not refute
it** — an infinite family is required, which is why this row needs the closed form rather than a
`decide` on one value.

## The shape of the argument

`main` refutes `Conj44`, the statement that some threshold `N` makes `(−1)^n S(n) ≥ 0` for all
`n ≥ N`.  Every `12u+30` is even, so the sign factor is `1` there, and `S_neg` shows the value is
negative — so no `N` can work.  The chain:

* `mem_sols` — a partition of `n` into parts from `{1,2,6}` is exactly a multiplicity vector
  `(a,b,c)` with `a + 2b + 6c = n`, and its number of parts is `tot (a,b,c) = a + b + c`.  This is
  a faithful rendering of "unordered partitions", not a reparametrisation assumed from the source.
* `S_eq_sols` — collapses the fibre sum: `∑_ℓ (−1)^ℓ ℓ² c(ℓ,n) = ∑_{(a,b,c)} (−1)^tot tot²`.
* `S_eq_bc` — eliminates `a = n − 2b − 6c`, giving the write-up's display (3).
* `S_eq_double` / `S_even_double` — the same sum with explicit ranges, and for even `n` the sign
  `(−1)^{b+c}` with an honest integer value.
* `alt_odd` / `alt_even` — the write-up's two alternating-sum identities, by induction.
* `pair_at` — the write-up's pairing: `c = 2r` instantiates `alt_odd` at `h = 3v+1` and `c = 2r+1`
  instantiates `alt_even` at `h = 3v`, their difference being `E_v − O_v = gterm j v` for
  `v = j − r`.
* `three_mul_S` — summing that over `v` via `sum_id` and `sum_sq` gives the closed form
  **`3·S(12j+6) = −(j+1)(52j²−61j−51)`**, stated multiplied by `3` so no division ever appears.
* `S_neg` — at `j = u+2` this is `−(u+3)(52u²+147u+35)`, negative because both factors are
  positive.

`S_thirty` records the write-up's stated first value `S(30) = −35`.

## Scope

This refutes Conjecture 4.4's second assertion at `m = 3`, `k = 2`.  The write-up leaves the
Baxter case `m = 3` of the *first* assertion undecided and claims **pending** campaign
eligibility because the final journal version could not be read; that is the collaborator's
accounting, not a mathematical qualification.  Nothing here depends on it.

## Checked in Python before formalizing

Exact integer/rational arithmetic, brute-force partition counting: the closed form against
`S_{{1,2,6},2}(12u+30)` for `u = 0…12` (values `−35, −312, −895, …, −46435`, all matching and all
negative); the double-sum display (3) against the partition count; `E_v` and `O_v` against brute
force for `j = 0…5` and every `r`; the two alternating-sum identities over `h = 0…11`,
`N = −5…29`; and the final `v`-summation symbolically in SymPy, including `j = u+2`.

Also recorded: `(−1)^n S < 0` holds far more densely than this family — for every `n ≥ 30` with
`n ≡ 2, 3 (mod 4)` in the range checked.  The write-up's progression is not the only failure, just
the one with a clean closed form.
-/

namespace Principia.MathDB.P353583

open Finset

/-- Multiplicity vectors `(a,b,c)` of partitions of `n` into parts from `{1,2,6}`:
`a` ones, `b` twos, `c` sixes. -/
def sols (n : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((range (n + 1)) ×ˢ (range (n + 1)) ×ˢ (range (n + 1))).filter
    (fun p => p.1 + 2 * p.2.1 + 6 * p.2.2 = n)

/-- The number of parts of the partition with multiplicity vector `p`. -/
def tot (p : ℕ × ℕ × ℕ) : ℕ := p.1 + p.2.1 + p.2.2

/-- Reduce `tot` on a literal triple.  Without this, `unfold tot` leaves `(a,b,c).2.1` standing
and `omega` treats each projection as an opaque atom — which cost a 336-second failing search. -/
@[simp] theorem tot_mk (a b c : ℕ) : tot (a, b, c) = a + b + c := rfl

/-- `c_{{1,2,6}}(ℓ, n)`: partitions of `n` into exactly `ℓ` parts from `{1,2,6}`. -/
def c126 (l n : ℕ) : ℕ := ((sols n).filter (fun p => tot p = l)).card

/-- `S_{{1,2,6},2}(n) = ∑_{ℓ=0}^{n} (−1)^ℓ ℓ² c(ℓ,n)`, the source's alternating weighted count. -/
def S (n : ℕ) : ℤ := ∑ l ∈ range (n + 1), (-1) ^ l * (l : ℤ) ^ 2 * (c126 l n : ℤ)

/-- Membership stated on a literal triple, so no `Prod` projection ever reaches `omega`. -/
theorem mem_sols (n a b c : ℕ) : (a, b, c) ∈ sols n ↔ a + 2 * b + 6 * c = n := by
  rw [sols, mem_filter]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    simp only [mem_product, mem_range]
    omega

/-- Every partition of `n` into parts `≥ 1` has at most `n` parts. -/
theorem tot_le (n : ℕ) (p : ℕ × ℕ × ℕ) (hp : p ∈ sols n) : tot p ≤ n := by
  obtain ⟨a, b, c⟩ := p
  rw [mem_sols] at hp
  rw [tot_mk]
  omega

/-- **Collapse the fibre sum.**  Grouping the multiplicity vectors by their number of parts turns
the `ℓ`-sum weighted by counts into a plain sum over solutions. -/
theorem S_eq_sols (n : ℕ) : S n = ∑ p ∈ sols n, (-1) ^ (tot p) * (tot p : ℤ) ^ 2 := by
  rw [← Finset.sum_fiberwise_of_maps_to
        (fun p hp => mem_range.mpr (Nat.lt_succ_of_le (tot_le n p hp)))
        (fun p => (-1) ^ (tot p) * (tot p : ℤ) ^ 2)]
  refine Finset.sum_congr rfl fun l _ => ?_
  have hfib : ∀ p ∈ (sols n).filter (fun p => tot p = l),
      (-1 : ℤ) ^ (tot p) * (tot p : ℤ) ^ 2 = (-1) ^ l * (l : ℤ) ^ 2 := by
    intro p hp; rw [mem_filter] at hp; rw [hp.2]
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, nsmul_eq_mul]
  unfold c126
  ring

/-- The `(b,c)` index set: `2b + 6c ≤ n`, i.e. the pairs for which `a = n − 2b − 6c` is a
legitimate nonnegative multiplicity. -/
def bc (n : ℕ) : Finset (ℕ × ℕ) :=
  ((range (n + 1)) ×ˢ (range (n + 1))).filter (fun q => 2 * q.1 + 6 * q.2 ≤ n)

theorem mem_bc (n b c : ℕ) : (b, c) ∈ bc n ↔ 2 * b + 6 * c ≤ n := by
  rw [bc, mem_filter]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    simp only [mem_product, mem_range]
    omega

/-- **The write-up's display (3).**  Eliminating `a = n − 2b − 6c` reparametrizes the sum by
`(b,c)`, with `tot = n − b − 5c`. -/
theorem S_eq_bc (n : ℕ) :
    S n = ∑ q ∈ bc n, (-1) ^ (n - q.1 - 5 * q.2) * ((n - q.1 - 5 * q.2 : ℕ) : ℤ) ^ 2 := by
  rw [S_eq_sols]
  refine Finset.sum_nbij' (fun p => (p.2.1, p.2.2)) (fun q => (n - 2 * q.1 - 6 * q.2, q.1, q.2))
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨a, b, c⟩ hp
    rw [mem_sols] at hp
    exact (mem_bc n b c).mpr (by omega)
  · rintro ⟨b, c⟩ hq
    rw [mem_bc] at hq
    exact (mem_sols n _ b c).mpr (by omega)
  · rintro ⟨a, b, c⟩ hp
    rw [mem_sols] at hp
    have ha : n - 2 * b - 6 * c = a := by omega
    simp only [ha]
  · rintro ⟨b, c⟩ _
    rfl
  · rintro ⟨a, b, c⟩ hp
    rw [mem_sols] at hp
    have h : tot (a, b, c) = n - b - 5 * c := by rw [tot_mk]; omega
    rw [h]

/-- `(-1)^k` depends only on `k % 2`. -/
theorem neg_one_pow_mod_two (k : ℕ) : (-1 : ℤ) ^ k = (-1) ^ (k % 2) := by
  conv_lhs => rw [← Nat.div_add_mod k 2]
  rw [pow_add, pow_mul]
  norm_num

/-- `∑_{b=0}^{2h+1} (−1)^b (N−b)² = (h+1)(2N−2h−1)`. -/
theorem alt_odd (N : ℤ) (h : ℕ) :
    ∑ b ∈ range (2 * h + 2), (-1 : ℤ) ^ b * (N - b) ^ 2 = (h + 1) * (2 * N - 2 * h - 1) := by
  induction h with
  | zero => simp [Finset.sum_range_succ] <;> ring
  | succ m ih =>
    have e : 2 * (m + 1) + 2 = 2 * m + 2 + 1 + 1 := by ring
    have h1 : (-1 : ℤ) ^ (2 * m + 2) = 1 := by rw [pow_add, pow_mul]; norm_num
    have h2 : (-1 : ℤ) ^ (2 * m + 2 + 1) = -1 := by rw [pow_succ, h1]; ring
    rw [e, Finset.sum_range_succ, Finset.sum_range_succ, ih, h1, h2]
    push_cast
    ring

/-- `∑_{b=0}^{2h} (−1)^b (N−b)² = N² − 2hN + 2h² + h`. -/
theorem alt_even (N : ℤ) (h : ℕ) :
    ∑ b ∈ range (2 * h + 1), (-1 : ℤ) ^ b * (N - b) ^ 2
      = N ^ 2 - 2 * h * N + 2 * h ^ 2 + h := by
  induction h with
  | zero => simp [Finset.sum_range_succ] <;> ring
  | succ m ih =>
    have e : 2 * (m + 1) + 1 = 2 * m + 1 + 1 + 1 := by ring
    have h1 : (-1 : ℤ) ^ (2 * m + 1) = -1 := by
      rw [pow_add, pow_mul]; norm_num
    have h2 : (-1 : ℤ) ^ (2 * m + 1 + 1) = 1 := by rw [pow_succ, h1]; ring
    rw [e, Finset.sum_range_succ, Finset.sum_range_succ, ih, h1, h2]
    push_cast
    ring

theorem sum_id (m : ℕ) : 2 * ∑ v ∈ range (m + 1), (v : ℤ) = m * (m + 1) := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    push_cast
    ring

theorem sum_sq (m : ℕ) : 6 * ∑ v ∈ range (m + 1), (v : ℤ) ^ 2 = m * (m + 1) * (2 * m + 1) := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    push_cast
    ring

/-- Split a range of even length into consecutive pairs. -/
theorem sum_range_two_mul (m : ℕ) (f : ℕ → ℤ) :
    ∑ c ∈ range (2 * m), f c = ∑ r ∈ range m, (f (2 * r) + f (2 * r + 1)) := by
  induction m with
  | zero => simp
  | succ k ih =>
    have e : 2 * (k + 1) = 2 * k + 1 + 1 := by ring
    rw [e, Finset.sum_range_succ, Finset.sum_range_succ, ih, Finset.sum_range_succ]
    ring

/-- Turn the `(b,c)` sum into an iterated sum with explicit ranges. -/
theorem S_eq_double (n : ℕ) :
    S n = ∑ c ∈ range (n / 6 + 1), ∑ b ∈ range ((n - 6 * c) / 2 + 1),
      (-1 : ℤ) ^ (n - b - 5 * c) * ((n - b - 5 * c : ℕ) : ℤ) ^ 2 := by
  rw [S_eq_bc, Finset.sum_sigma']
  refine Finset.sum_nbij' (fun q => (⟨q.2, q.1⟩ : (_ : ℕ) × ℕ))
    (fun x => (x.2, x.1)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨b, c⟩ hq
    rw [mem_bc] at hq
    simp only [Finset.mem_sigma, mem_range]
    omega
  · rintro ⟨c, b⟩ hx
    simp only [Finset.mem_sigma, mem_range] at hx
    -- `rw [mem_bc]` leaves the GOAL carrying `⟨c,b⟩.fst/.snd`, which omega treats as atoms;
    -- `exact _.mpr` unifies up to defeq instead.
    exact (mem_bc n b c).mpr (by omega)
  · rintro ⟨b, c⟩ _
    rfl
  · rintro ⟨c, b⟩ _
    rfl
  · rintro ⟨b, c⟩ _
    rfl

/-- For even `n` the sign is `(−1)^{b+c}` and the value is an honest integer. -/
theorem S_even_double (n : ℕ) (hn : n % 2 = 0) :
    S n = ∑ c ∈ range (n / 6 + 1), ∑ b ∈ range ((n - 6 * c) / 2 + 1),
      (-1 : ℤ) ^ (b + c) * ((n : ℤ) - b - 5 * c) ^ 2 := by
  rw [S_eq_double]
  refine Finset.sum_congr rfl fun c hc => Finset.sum_congr rfl fun b hb => ?_
  rw [mem_range] at hc hb
  have hs : (-1 : ℤ) ^ (n - b - 5 * c) = (-1) ^ (b + c) := by
    rw [neg_one_pow_mod_two (n - b - 5 * c), neg_one_pow_mod_two (b + c)]
    congr 1
    omega
  have hcast : ((n - b - 5 * c : ℕ) : ℤ) = (n : ℤ) - b - 5 * c := by omega
  rw [hs, hcast]

/-- The summand `E_v − O_v` of the write-up. -/
def gterm (j v : ℕ) : ℤ :=
  -16 * (v : ℤ) ^ 2 + (38 - 16 * (j : ℤ)) * v - 4 * (j : ℤ) ^ 2 + 4 * (j : ℤ) + 17

/-- Linearity of the `v`-sum, with the range endpoint generalized so it is an induction. -/
theorem gterm_split (j m : ℕ) :
    ∑ v ∈ range m, gterm j v
      = -16 * (∑ v ∈ range m, (v : ℤ) ^ 2) + (38 - 16 * (j : ℤ)) * (∑ v ∈ range m, (v : ℤ))
        + m * (-4 * (j : ℤ) ^ 2 + 4 * (j : ℤ) + 17) := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, ih]
    simp only [gterm]
    push_cast
    ring

/-- The write-up's pairing: `c = 2r` uses `alt_odd` at `h = 3v+1`, `c = 2r+1` uses `alt_even`
at `h = 3v`, and their difference is `E_v - O_v = gterm j v`, where `v = j - r`. -/
theorem pair_at (j r v : ℕ) (hv : r + v = j) :
    (∑ b ∈ range ((12 * j + 6 - 6 * (2 * r)) / 2 + 1),
        (-1 : ℤ) ^ (b + 2 * r) * (12 * (j : ℤ) + 6 - b - 5 * (2 * (r : ℤ))) ^ 2)
      + (∑ b ∈ range ((12 * j + 6 - 6 * (2 * r + 1)) / 2 + 1),
        (-1 : ℤ) ^ (b + (2 * r + 1)) * (12 * (j : ℤ) + 6 - b - 5 * (2 * (r : ℤ) + 1)) ^ 2)
    = gterm j v := by
  have hr1 : (12 * j + 6 - 6 * (2 * r)) / 2 + 1 = 2 * (3 * v + 1) + 2 := by omega
  have hr2 : (12 * j + 6 - 6 * (2 * r + 1)) / 2 + 1 = 2 * (3 * v) + 1 := by omega
  have hsq : (-1 : ℤ) ^ (2 * r) = 1 := by rw [pow_mul]; norm_num
  have e1 : ∀ b : ℕ, (-1 : ℤ) ^ (b + 2 * r) * (12 * (j : ℤ) + 6 - b - 5 * (2 * (r : ℤ))) ^ 2
      = (-1 : ℤ) ^ b * ((12 * (j : ℤ) + 6 - 10 * (r : ℤ)) - b) ^ 2 := by
    intro b
    rw [pow_add, hsq, mul_one]
    ring
  have e2 : ∀ b : ℕ,
      (-1 : ℤ) ^ (b + (2 * r + 1)) * (12 * (j : ℤ) + 6 - b - 5 * (2 * (r : ℤ) + 1)) ^ 2
      = -((-1 : ℤ) ^ b * ((12 * (j : ℤ) + 6 - 10 * (r : ℤ) - 5) - b) ^ 2) := by
    intro b
    rw [show b + (2 * r + 1) = b + 2 * r + 1 from by ring, pow_succ, pow_add, hsq, mul_one]
    ring
  rw [hr1, hr2, Finset.sum_congr rfl (fun b _ => e1 b), Finset.sum_congr rfl (fun b _ => e2 b),
    Finset.sum_neg_distrib, alt_odd, alt_even]
  simp only [gterm]
  subst hv
  push_cast
  ring

/-- **The closed form, division-free.**  `3·S(12j+6) = −(j+1)(52j²−61j−51)`. -/
theorem three_mul_S (j : ℕ) :
    3 * S (12 * j + 6) = -((j : ℤ) + 1) * (52 * (j : ℤ) ^ 2 - 61 * (j : ℤ) - 51) := by
  have hr : (12 * j + 6) / 6 + 1 = 2 * (j + 1) := by omega
  rw [S_even_double (12 * j + 6) (by omega), hr, sum_range_two_mul]
  push_cast
  rw [Finset.sum_congr rfl (fun r hr => pair_at j r (j - r) (by
    rw [mem_range] at hr; omega))]
  have hrefl := Finset.sum_range_reflect (gterm j) (j + 1)
  simp only [Nat.add_sub_cancel] at hrefl
  rw [hrefl, gterm_split]
  have h1 := sum_id j
  have h2 := sum_sq j
  push_cast
  linear_combination (-8 : ℤ) * h2 + (57 - 24 * (j : ℤ)) * h1

/-- The write-up's first value on the progression: `S(30) = -35`. -/
theorem S_thirty : S 30 = -35 := by
  have h := three_mul_S 2
  norm_num at h
  linarith

/-- `S(12u+30) < 0` for every `u`: the factors `(u+3)` and `52u²+147u+35` are both positive. -/
theorem S_neg (u : ℕ) : S (12 * u + 30) < 0 := by
  have h := three_mul_S (u + 2)
  have e : 12 * (u + 2) + 6 = 12 * u + 30 := by ring
  rw [e] at h
  have hu : (0 : ℤ) ≤ (u : ℤ) := Int.natCast_nonneg u
  push_cast at h
  nlinarith [h, hu, sq_nonneg ((u : ℤ))]

/-- **Conjecture 4.4** for `U_3 = {1,2,6}` and `k = 2`: `(-1)^n S(n) ≥ 0` for all large `n`. -/
def Conj44 : Prop := ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 0 ≤ (-1 : ℤ) ^ n * S n

/-- **MathDB #353583 — Conjecture 4.4 is FALSE.**  No threshold works: every `12u+30` is even,
so the sign factor is `1` there, while `S(12u+30) < 0`. -/
theorem main : ¬ Conj44 := by
  rintro ⟨N, hN⟩
  have h := hN (12 * N + 30) (by omega)
  have hpar : (-1 : ℤ) ^ (12 * N + 30) = 1 := by
    rw [show 12 * N + 30 = 2 * (6 * N + 15) from by ring, pow_mul]
    norm_num
  rw [hpar, one_mul] at h
  exact absurd h (not_le.mpr (S_neg N))

end Principia.MathDB.P353583
