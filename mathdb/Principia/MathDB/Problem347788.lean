import Mathlib

/-!
# MathDB #347788 — the Dilcher–Ulas block conjecture

Write-up `mathdb-open-problems/problems/347788/solution.tex`,
*Positivity and monotonicity of the Dilcher–Ulas sequence in every block*, 18 September 2026.

With `f_{m,n}(z) = ∑_a C(n,a) z^{C(a,m)}` and `f_{m,n} = f_{m,n}(-1)`, Dilcher–Ulas
Conjecture 5.8 asserts, for `m = 2^k`,

`0 < (−1)^ν f_{m,2mν} < (−1)^ν f_{m,2mν+1} < ⋯ < (−1)^ν f_{m,2mν+2m−3}
   = (−1)^ν f_{m,2mν+2m−2}`,  with  `f_{m,2mν+2m−1} = 0`.

`main` proves all of it, for every `k ≥ 1` and every block index `ν`, about the source's own
sequence `fsrc K n = ∑_a C(n,a) (−1)^{C(a,2^K)}` — not about a parity surrogate.

## The route, and why it is not the write-up's

The write-up goes through the adjacency matrix of a path graph, Chebyshev polynomials and finite
Fourier inversion.  **None of that is needed**, and none of it is used here.

*The bridge.*  `choose_two_pow_modEq` is **Lucas's theorem at `p = 2`**: `C(a,2^K) ≡ ⌊a/2^K⌋
(mod 2)`, by induction on `K` off Mathlib's `Choose.choose_modEq_choose_mod_mul_choose_div_nat`.
So the source's sign `(−1)^{C(a,m)}` IS the antiperiodic `σ(a) = (−1)^{⌊a/m⌋}`
(`neg_one_pow_choose_eq_sgn`), and `fsrc K = Gv (2^K) 0` (`fsrc_eq`).  The parity reduction is
*proved*, not assumed.

*The engine.*  Put `G_j(n) = ∑_a C(n,a) σ(a+j)`.  Pascal's rule and antiperiodicity give

* `Gv_succ` — `G_j(n+1) = G_j(n) + G_{j+1}(n)`;
* `Gv_wrap` — `G_{j+m} = −G_j`;
* `Gv_antisym` — **`G_a(n) + G_b(n) = 0` whenever `2m ∣ a + b + n + 1`**, whose induction step
  is two applications of the hypothesis, since `a + (b+1) + n + 1` and `(a+1) + b + n + 1` are
  both `a + b + (n+1) + 1`.

*The invariant.*  The whole vector `V(n) = (G_0,…,G_{m−1})(n)` has a forced sign pattern inside
each block: `+^{m−t} −^{t}` at `n = N + 2t` and `+^{m−t−1} 0 −^{t}` at `n = N + 2t+1`, up to the
global sign `(−1)^ν`.  `step_to_even` is free — every coordinate is a sum of two entries that
are never strictly opposite in sign.  `step_to_odd` has **exactly one** coordinate whose two
summands do disagree, and that coordinate is precisely a zero of `Gv_antisym`: at `j = m−t−1`
the divisor is `2m + N`, so the block-start hypothesis `2m ∣ N` is what makes it available.
`block_start` then flips the sign from block to block, and `block_pattern` is the induction.

*The payoff.*  `f(n+1) − f(n) = G_1(n)` is just `Gv_succ` at `j = 0`, so all three assertions are
statements about ONE coordinate: `second_coord` is the strict rise, `second_coord_zero` the equal
final pair (the pattern's zero at `t = m−2`), and `Gv_zero_at` the vanishing.

## Scope

Proved for **every `m ≥ 2`** (`block_conjecture`), not only powers of two — the restriction
`m = 2^k` is needed only for the Lucas bridge to the source's binomial exponent.  `m = 1` is
genuinely excluded: there `f_{1,n} = (1-1)^n = 0` for all `n ≥ 1`.

## A note on tactic limits met here

`omega` cannot reduce `% (2*m)` or `a / m` for a VARIABLE `m` — both are nonlinear in its sense,
and it treats a product `2*m*c` of two variables as an opaque atom.  So the hypothesis of
`Gv_antisym` is stated with `∣` rather than `%` (divisibility transports through the induction
with no arithmetic at all), `sgn` is characterised by `sgn_of_lt`/`sgn_of_mid`/`sgn_period`
instead of by its defining `/`, and every step that compares `2*m*(c+1)` with `2*m*c` is handed
the expansion as a `ring`-proved `have` first.

Checked in Python before formalizing (`explore_347788.py`, `verify_347788_signs.py`): the
recurrence and the wrap for `m = 2,3,4,8`; the structural law over 682 index pairs; the uniform
sign prediction from `σ = 2j+n mod 4m` with **zero mismatches** over `m = 2..9`, `n ≤ 6m+1`,
`j ≤ 3m+1`, together with the failure at `m = 1` that forces the hypothesis; that exactly two
residue classes per period need an external zero; and the three conjecture assertions on the
LITERAL sequence `∑_a C(n,a)(−1)^{C(a,m)}` for `m = 2,4,8`.
-/

namespace Principia.MathDB.P347788

open Finset

/-- The source's antiperiodic sign sequence `σ(a) = (−1)^⌊a/m⌋`. -/
def sgn (m a : ℕ) : ℤ := (-1) ^ (a / m)

/-- `G_j(n) = ∑_a C(n,a) σ(a+j)`.  At `j = 0` this is the source's `F_m(n)`. -/
def Gv (m j n : ℕ) : ℤ := ∑ a ∈ range (n + 1), (n.choose a : ℤ) * sgn m (a + j)

/-- **Pascal's rule gives an elementary recurrence**, replacing the write-up's Fourier route. -/
theorem Gv_succ (m j n : ℕ) : Gv m j (n + 1) = Gv m j n + Gv m (j + 1) n := by
  unfold Gv
  rw [Finset.sum_range_succ' (fun a => ((n + 1).choose a : ℤ) * sgn m (a + j)) (n + 1)]
  have hlast : ∀ a ∈ range (n + 1),
      (((n + 1).choose (a + 1) : ℤ)) * sgn m (a + 1 + j)
        = (n.choose a : ℤ) * sgn m (a + 1 + j) + (n.choose (a + 1) : ℤ) * sgn m (a + 1 + j) := by
    intro a _
    rw [Nat.choose_succ_succ]
    push_cast
    ring
  rw [Finset.sum_congr rfl hlast, Finset.sum_add_distrib]
  have e1 : ∑ a ∈ range (n + 1), (n.choose a : ℤ) * sgn m (a + 1 + j)
      = ∑ a ∈ range (n + 1), (n.choose a : ℤ) * sgn m (a + (j + 1)) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    congr 2
    omega
  have e2 : (∑ a ∈ range (n + 1), (n.choose (a + 1) : ℤ) * sgn m (a + 1 + j))
        + ((n + 1).choose 0 : ℤ) * sgn m (0 + j)
      = ∑ a ∈ range (n + 1), (n.choose a : ℤ) * sgn m (a + j) := by
    rw [Finset.sum_range_succ' (fun a => (n.choose a : ℤ) * sgn m (a + j)) n]
    rw [Finset.sum_range_succ (fun a => (n.choose (a + 1) : ℤ) * sgn m (a + 1 + j)) n]
    simp [Nat.choose_succ_self]
  rw [e1]
  linarith [e2]

/-- Antiperiodicity: shifting the index by `m` flips the sign. -/
theorem sgn_add (m a : ℕ) (hm : 0 < m) : sgn m (a + m) = - sgn m a := by
  unfold sgn
  rw [Nat.add_div_right a hm, pow_succ]
  ring

/-- The vector wraps antiperiodically: `G_{j+m} = -G_j`.  With `Gv_succ` this makes
`(G_0,…,G_{m-1})` evolve by a FIXED integer matrix, which is the whole content the write-up
obtains through finite Fourier inversion. -/
theorem Gv_wrap (m j n : ℕ) (hm : 0 < m) : Gv m (j + m) n = - Gv m j n := by
  unfold Gv
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  have e : a + (j + m) = (a + j) + m := by omega
  rw [e, sgn_add m (a + j) hm]
  ring

theorem Gv_at_zero (m j : ℕ) : Gv m j 0 = sgn m j := by
  unfold Gv
  simp

/-- `sgn` is `1` below the antiperiod. -/
theorem sgn_of_lt (m j : ℕ) (h : j < m) : sgn m j = 1 := by
  unfold sgn
  rw [Nat.div_eq_of_lt h]
  norm_num

/-- and `-1` on the second half-period. -/
theorem sgn_of_mid (m j : ℕ) (h1 : m ≤ j) (h2 : j < 2 * m) : sgn m j = -1 := by
  unfold sgn
  have hm : 0 < m := by omega
  have : j / m = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
  rw [this]
  norm_num

/-- `sgn` has period `2m`. -/
theorem sgn_period (m j : ℕ) (hm : 0 < m) : sgn m (j + 2 * m) = sgn m j := by
  have e : j + 2 * m = (j + m) + m := by omega
  rw [e, sgn_add m (j + m) hm, sgn_add m j hm]
  ring

/-- The two signs cancel exactly when the antiperiod `2m` divides `a + b + 1`.
Divisibility rather than `%` because `omega` cannot reduce `% (2*m)` for a VARIABLE `m`, while
`∣` transports through the induction with no arithmetic at all. -/
theorem sgn_pair (m : ℕ) (hm : 0 < m) :
    ∀ (N a b : ℕ), a + b = N → 2 * m ∣ (a + b + 1) → sgn m a + sgn m b = 0 := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro a b hab hdvd
    by_cases hA : 2 * m ≤ a
    · obtain ⟨a', rfl⟩ : ∃ a', a = a' + 2 * m := ⟨a - 2 * m, by omega⟩
      rw [sgn_period m a' hm]
      refine ih (a' + b) (by omega) a' b rfl ?_
      have e : a' + 2 * m + b + 1 = (a' + b + 1) + 2 * m := by ring
      rw [e] at hdvd
      exact (Nat.dvd_add_iff_left (dvd_refl (2 * m))).mpr hdvd
    · by_cases hB : 2 * m ≤ b
      · obtain ⟨b', rfl⟩ : ∃ b', b = b' + 2 * m := ⟨b - 2 * m, by omega⟩
        rw [sgn_period m b' hm]
        refine ih (a + b') (by omega) a b' rfl ?_
        have e : a + (b' + 2 * m) + 1 = (a + b' + 1) + 2 * m := by ring
        rw [e] at hdvd
        exact (Nat.dvd_add_iff_left (dvd_refl (2 * m))).mpr hdvd
      · push_neg at hA hB
        obtain ⟨c, hc⟩ := hdvd
        have hc1 : c = 1 := by
          rcases c with _ | c
          · omega
          · rcases c with _ | c
            · rfl
            · exfalso
              have : 2 * m * 2 ≤ 2 * m * (c + 1 + 1) :=
                Nat.mul_le_mul_left _ (by omega)
              omega
        rw [hc1, mul_one] at hc
        by_cases hlt : a < m
        · rw [sgn_of_lt m a hlt, sgn_of_mid m b (by omega) (by omega)]
          ring
        · push_neg at hlt
          rw [sgn_of_mid m a hlt (by omega), sgn_of_lt m b (by omega)]
          ring

/-- **The structural law.**  `G_a(n) + G_b(n) = 0` whenever `a + b + n + 1 ≡ 0 (mod 2m)`.
The induction step is two applications of the hypothesis, because both
`a + (b+1) + n + 1` and `(a+1) + b + n + 1` equal `a + b + (n+1) + 1`. -/
theorem Gv_antisym (m : ℕ) (hm : 0 < m) :
    ∀ (n a b : ℕ), 2 * m ∣ (a + b + n + 1) → Gv m a n + Gv m b n = 0 := by
  intro n
  induction n with
  | zero =>
    intro a b h
    rw [Gv_at_zero, Gv_at_zero]
    refine sgn_pair m hm (a + b) a b rfl ?_
    have e : a + b + 1 = a + b + 0 + 1 := by omega
    rw [e]; exact h
  | succ k ih =>
    intro a b h
    rw [Gv_succ, Gv_succ]
    have e1 : a + (b + 1) + k + 1 = a + b + (k + 1) + 1 := by omega
    have e2 : (a + 1) + b + k + 1 = a + b + (k + 1) + 1 := by omega
    have d1 : 2 * m ∣ (a + (b + 1) + k + 1) := by rw [e1]; exact h
    have d2 : 2 * m ∣ ((a + 1) + b + k + 1) := by rw [e2]; exact h
    have r1 := ih a (b + 1) d1
    have r2 := ih (a + 1) b d2
    linarith

/-! ### Part 1 — the Lucas bridge from the source's `f_{m,n}` to `Gv` -/

/-- `(-1)^e` depends only on `e mod 2`. -/
theorem neg_one_pow_congr {x y : ℕ} (h : x ≡ y [MOD 2]) : (-1 : ℤ) ^ x = (-1) ^ y := by
  have hx : x % 2 = y % 2 := h
  conv_lhs => rw [← Nat.div_add_mod x 2]
  conv_rhs => rw [← Nat.div_add_mod y 2]
  rw [pow_add, pow_add, pow_mul, pow_mul, hx]
  norm_num

/-- **Lucas at `p = 2`**: `C(a, 2^K) ≡ ⌊a / 2^K⌋ (mod 2)`. -/
theorem choose_two_pow_modEq (K : ℕ) : ∀ a : ℕ, a.choose (2 ^ K) ≡ a / 2 ^ K [MOD 2] := by
  induction K with
  | zero => intro a; simpa using Nat.ModEq.refl a
  | succ k ih =>
    intro a
    have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hl : a.choose (2 ^ (k + 1))
        ≡ (a % 2).choose (2 ^ (k + 1) % 2) * (a / 2).choose (2 ^ (k + 1) / 2) [MOD 2] :=
      Choose.choose_modEq_choose_mod_mul_choose_div_nat
    have hmod : 2 ^ (k + 1) % 2 = 0 := by
      have : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
      omega
    have hdiv : 2 ^ (k + 1) / 2 = 2 ^ k := by
      have : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
      omega
    rw [hmod, hdiv, Nat.choose_zero_right, one_mul] at hl
    have he : a / 2 ^ (k + 1) = (a / 2) / 2 ^ k := by
      rw [Nat.div_div_eq_div_mul]
      congr 1
      ring
    rw [he]
    exact hl.trans (ih (a / 2))

/-- The source's sign `(−1)^{C(a,m)}` at `m = 2^K` IS the antiperiodic sign `σ(a)`. -/
theorem neg_one_pow_choose_eq_sgn (K a : ℕ) :
    (-1 : ℤ) ^ (a.choose (2 ^ K)) = sgn (2 ^ K) a :=
  neg_one_pow_congr (choose_two_pow_modEq K a)

/-- **The source's sequence itself**: `f_{m,n} = ∑_a C(n,a) (−1)^{C(a,m)}` at `m = 2^K`. -/
def fsrc (K n : ℕ) : ℤ := ∑ a ∈ range (n + 1), (n.choose a : ℤ) * (-1) ^ (a.choose (2 ^ K))

theorem fsrc_eq (K n : ℕ) : fsrc K n = Gv (2 ^ K) 0 n := by
  unfold fsrc Gv
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [neg_one_pow_choose_eq_sgn K a, Nat.add_zero]

/-! ### Part 2 — the sign pattern -/

/-- The wrap at the top coordinate. -/
theorem Gv_top (m n : ℕ) (hm : 0 < m) : Gv m m n = - Gv m 0 n := by
  simpa using Gv_wrap m 0 n hm

/-- **Even row → odd row.**  The only step that is not a sum of like signs is the middle
coordinate, and that one is exactly the zero supplied by `Gv_antisym`. -/
theorem step_to_odd (m : ℕ) (hm : 2 ≤ m) (ε : ℤ) (N t : ℕ) (hN : 2 * m ∣ N) (ht : t < m)
    (hev : ∀ j, j < m → (j + t < m → 0 < ε * Gv m j (N + 2 * t))
                      ∧ (m ≤ j + t → ε * Gv m j (N + 2 * t) < 0)) :
    ∀ j, j < m → (j + t + 1 < m → 0 < ε * Gv m j (N + 2 * t + 1))
               ∧ (j + t + 1 = m → Gv m j (N + 2 * t + 1) = 0)
               ∧ (m < j + t + 1 → ε * Gv m j (N + 2 * t + 1) < 0) := by
  have hm0 : 0 < m := by omega
  -- extend the even row to the wrapped coordinate `k = m`
  have hev' : ∀ k, k ≤ m → (k + t < m → 0 < ε * Gv m k (N + 2 * t))
                         ∧ (m ≤ k + t → ε * Gv m k (N + 2 * t) < 0) := by
    intro k hk
    rcases lt_or_eq_of_le hk with h | h
    · exact hev k h
    · refine ⟨fun hcon => absurd hcon (by omega), fun _ => ?_⟩
      rw [h, Gv_top m (N + 2 * t) hm0]
      have := (hev 0 hm0).1 (by omega)
      linarith [this]
  intro j hj
  have hsucc : Gv m j (N + 2 * t + 1) = Gv m j (N + 2 * t) + Gv m (j + 1) (N + 2 * t) :=
    Gv_succ m j (N + 2 * t)
  refine ⟨fun h1 => ?_, fun h2 => ?_, fun h3 => ?_⟩
  · have a1 := (hev' j (by omega)).1 (by omega)
    have a2 := (hev' (j + 1) (by omega)).1 (by omega)
    rw [hsucc, mul_add]
    linarith
  · -- the middle coordinate: `2m ∣ j + j + (N + 2t + 1) + 1` because `j = m − t − 1`
    have hdvd : 2 * m ∣ (j + j + (N + 2 * t + 1) + 1) := by
      obtain ⟨c, hc⟩ := hN
      refine ⟨c + 1, ?_⟩
      have hexp : 2 * m * (c + 1) = 2 * m * c + 2 * m := by ring
      have hjt : j + t + 1 = m := h2
      omega
    have := Gv_antisym m hm0 (N + 2 * t + 1) j j hdvd
    linarith
  · have a1 := (hev' j (by omega)).2 (by omega)
    have a2 := (hev' (j + 1) (by omega)).2 (by omega)
    rw [hsucc, mul_add]
    linarith

/-- **Odd row → next even row.**  Every coordinate is a sum of two entries that are never
strictly opposite in sign, so no new input is needed here. -/
theorem step_to_even (m : ℕ) (hm : 2 ≤ m) (ε : ℤ) (N t : ℕ) (ht : t < m)
    (hodd : ∀ j, j < m → (j + t + 1 < m → 0 < ε * Gv m j (N + 2 * t + 1))
                       ∧ (j + t + 1 = m → Gv m j (N + 2 * t + 1) = 0)
                       ∧ (m < j + t + 1 → ε * Gv m j (N + 2 * t + 1) < 0)) :
    ∀ j, j < m → (j + (t + 1) < m → 0 < ε * Gv m j (N + 2 * (t + 1)))
               ∧ (m ≤ j + (t + 1) → ε * Gv m j (N + 2 * (t + 1)) < 0) := by
  have hm0 : 0 < m := by omega
  intro j hj
  have hidx : N + 2 * (t + 1) = (N + 2 * t + 1) + 1 := by ring
  have hsucc : Gv m j (N + 2 * (t + 1))
      = Gv m j (N + 2 * t + 1) + Gv m (j + 1) (N + 2 * t + 1) := by
    rw [hidx]; exact Gv_succ m j (N + 2 * t + 1)
  by_cases hjm : j + 1 < m
  · -- both coordinates are inside the window
    obtain ⟨p1, p2, p3⟩ := hodd j hj
    obtain ⟨q1, q2, q3⟩ := hodd (j + 1) hjm
    refine ⟨fun h1 => ?_, fun h2 => ?_⟩
    · have ha : 0 < ε * Gv m j (N + 2 * t + 1) := p1 (by omega)
      have hb : 0 ≤ ε * Gv m (j + 1) (N + 2 * t + 1) := by
        rcases Nat.lt_or_ge (j + 1 + t + 1) m with h | h
        · exact le_of_lt (q1 h)
        · have : j + 1 + t + 1 = m := by omega
          rw [q2 this]; simp
      rw [hsucc, mul_add]; linarith
    · have hb : ε * Gv m (j + 1) (N + 2 * t + 1) < 0 := q3 (by omega)
      have ha : ε * Gv m j (N + 2 * t + 1) ≤ 0 := by
        rcases Nat.lt_or_ge m (j + t + 1) with h | h
        · exact le_of_lt (p3 h)
        · have : j + t + 1 = m := by omega
          rw [p2 this]; simp
      rw [hsucc, mul_add]; linarith
  · -- `j = m − 1`: the partner is the wrapped coordinate `−G_0`
    have hj1 : j + 1 = m := by omega
    obtain ⟨p1, p2, p3⟩ := hodd j hj
    obtain ⟨r1, r2, r3⟩ := hodd 0 hm0
    refine ⟨by omega, fun _ => ?_⟩
    have hwrap : Gv m (j + 1) (N + 2 * t + 1) = - Gv m 0 (N + 2 * t + 1) := by
      rw [hj1]; exact Gv_top m (N + 2 * t + 1) hm0
    have ha : ε * Gv m j (N + 2 * t + 1) ≤ 0 := by
      rcases Nat.lt_or_ge m (j + t + 1) with h | h
      · exact le_of_lt (p3 h)
      · have : j + t + 1 = m := by omega
        rw [p2 this]; simp
    have hb : 0 ≤ ε * Gv m 0 (N + 2 * t + 1) := by
      rcases Nat.lt_or_ge (0 + t + 1) m with h | h
      · exact le_of_lt (r1 h)
      · have : 0 + t + 1 = m := by omega
        rw [r2 this]; simp
    -- strictness: at most one of the two summands can vanish, since `m ≥ 2`
    have hstrict : ε * Gv m j (N + 2 * t + 1) < 0 ∨ 0 < ε * Gv m 0 (N + 2 * t + 1) := by
      rcases Nat.lt_or_ge m (j + t + 1) with h | h
      · exact Or.inl (p3 h)
      · have hjt : j + t + 1 = m := by omega
        have : t = 0 := by omega
        exact Or.inr (r1 (by omega))
    rw [hsucc, hwrap, mul_add, mul_neg]
    rcases hstrict with h | h <;> linarith

/-- **The block pattern.**  Starting from a row that is uniformly of sign `ε` at a time divisible
by `2m`, the whole block's signs are forced: `+^{m−t} −^{t}` at even offsets and
`+^{m−t−1} 0 −^{t}` at odd ones. -/
theorem block_pattern (m : ℕ) (hm : 2 ≤ m) (ε : ℤ) (N : ℕ) (hN : 2 * m ∣ N)
    (hstart : ∀ j, j < m → 0 < ε * Gv m j N) :
    ∀ t, t ≤ m →
      (∀ j, j < m → (j + t < m → 0 < ε * Gv m j (N + 2 * t))
                  ∧ (m ≤ j + t → ε * Gv m j (N + 2 * t) < 0))
    ∧ (t < m → ∀ j, j < m → (j + t + 1 < m → 0 < ε * Gv m j (N + 2 * t + 1))
                  ∧ (j + t + 1 = m → Gv m j (N + 2 * t + 1) = 0)
                  ∧ (m < j + t + 1 → ε * Gv m j (N + 2 * t + 1) < 0)) := by
  intro t
  induction t with
  | zero =>
    intro _
    have hev : ∀ j, j < m → (j + 0 < m → 0 < ε * Gv m j (N + 2 * 0))
                          ∧ (m ≤ j + 0 → ε * Gv m j (N + 2 * 0) < 0) := by
      intro j hj
      refine ⟨fun _ => ?_, fun h => by omega⟩
      simpa using hstart j hj
    exact ⟨hev, fun h0 => step_to_odd m hm ε N 0 hN h0 hev⟩
  | succ s ih =>
    intro hs
    have hsm : s < m := by omega
    obtain ⟨_, hodd⟩ := ih (by omega)
    have hev' := step_to_even m hm ε N s hsm (hodd hsm)
    refine ⟨hev', fun hlt => ?_⟩
    have hidx : N + 2 * (s + 1) = N + 2 * (s + 1) := rfl
    exact step_to_odd m hm ε N (s + 1) hN hlt hev'

/-- **Every block starts uniformly positive up to the global sign `(−1)^ν`.** -/
theorem block_start (m : ℕ) (hm : 2 ≤ m) :
    ∀ ν j, j < m → 0 < (-1 : ℤ) ^ ν * Gv m j (2 * m * ν) := by
  intro ν
  induction ν with
  | zero =>
    intro j hj
    have : Gv m j (2 * m * 0) = 1 := by
      simpa using (Gv_at_zero m j).trans (sgn_of_lt m j hj)
    rw [this]; norm_num
  | succ k ih =>
    intro j hj
    have hN : 2 * m ∣ 2 * m * k := ⟨k, rfl⟩
    have hpat := block_pattern m hm ((-1 : ℤ) ^ k) (2 * m * k) hN ih m (le_refl m)
    have hneg := (hpat.1 j hj).2 (by omega)
    have hidx : 2 * m * (k + 1) = 2 * m * k + 2 * m := by ring
    rw [hidx, pow_succ]
    have hfold : (-1 : ℤ) ^ k * -1 * Gv m j (2 * m * k + 2 * m)
        = -((-1 : ℤ) ^ k * Gv m j (2 * m * k + 2 * m)) := by ring
    rw [hfold]
    linarith

/-! ### Part 3 — the three assertions of the conjecture -/

/-- **The vanishing**, for every block index. -/
theorem Gv_zero_at (m : ℕ) (hm : 2 ≤ m) (ν : ℕ) : Gv m 0 (2 * m * ν + (2 * m - 1)) = 0 := by
  have hm0 : 0 < m := by omega
  have hdvd : 2 * m ∣ (0 + 0 + (2 * m * ν + (2 * m - 1)) + 1) := by
    refine ⟨ν + 1, ?_⟩
    have hexp : 2 * m * (ν + 1) = 2 * m * ν + 2 * m := by ring
    omega
  have := Gv_antisym m hm0 (2 * m * ν + (2 * m - 1)) 0 0 hdvd
  linarith

/-- **The increments are the second coordinate**, and it is positive on the whole rising part. -/
theorem second_coord (m : ℕ) (hm : 2 ≤ m) (ν i : ℕ) (hi : i + 3 < 2 * m) :
    0 < (-1 : ℤ) ^ ν * Gv m 1 (2 * m * ν + i) := by
  have hN : 2 * m ∣ 2 * m * ν := ⟨ν, rfl⟩
  have hstart := block_start m hm ν
  rcases Nat.even_or_odd i with ⟨t, ht⟩ | ⟨t, ht⟩
  · have hti : i = 2 * t := by omega
    have hpat := block_pattern m hm ((-1 : ℤ) ^ ν) (2 * m * ν) hN hstart t (by omega)
    have := (hpat.1 1 (by omega)).1 (by omega)
    rw [hti]
    exact this
  · have hti : i = 2 * t + 1 := by omega
    have hpat := block_pattern m hm ((-1 : ℤ) ^ ν) (2 * m * ν) hN hstart t (by omega)
    have := ((hpat.2 (by omega)) 1 (by omega)).1 (by omega)
    rw [hti, ← Nat.add_assoc]
    exact this

/-- and it vanishes at the one place the conjecture asserts an equal pair. -/
theorem second_coord_zero (m : ℕ) (hm : 2 ≤ m) (ν : ℕ) :
    Gv m 1 (2 * m * ν + (2 * m - 3)) = 0 := by
  have hN : 2 * m ∣ 2 * m * ν := ⟨ν, rfl⟩
  have hstart := block_start m hm ν
  have hpat := block_pattern m hm ((-1 : ℤ) ^ ν) (2 * m * ν) hN hstart (m - 2) (by omega)
  have hz := ((hpat.2 (by omega)) 1 (by omega)).2.1 (by omega)
  have he : 2 * m * ν + 2 * (m - 2) + 1 = 2 * m * ν + (2 * m - 3) := by omega
  rw [he] at hz
  exact hz

/-- **The source's conjecture, in full, for every `m ≥ 2` and every block index `ν`.** -/
theorem block_conjecture (m : ℕ) (hm : 2 ≤ m) (ν : ℕ) :
    0 < (-1 : ℤ) ^ ν * Gv m 0 (2 * m * ν)
  ∧ (∀ i, i + 3 < 2 * m → (-1 : ℤ) ^ ν * Gv m 0 (2 * m * ν + i)
        < (-1 : ℤ) ^ ν * Gv m 0 (2 * m * ν + (i + 1)))
  ∧ Gv m 0 (2 * m * ν + (2 * m - 3)) = Gv m 0 (2 * m * ν + (2 * m - 2))
  ∧ Gv m 0 (2 * m * ν + (2 * m - 1)) = 0 := by
  refine ⟨block_start m hm ν 0 (by omega), fun i hi => ?_, ?_, Gv_zero_at m hm ν⟩
  · have he : 2 * m * ν + (i + 1) = (2 * m * ν + i) + 1 := by omega
    rw [he, Gv_succ, mul_add]
    have := second_coord m hm ν i hi
    linarith
  · have he : 2 * m * ν + (2 * m - 2) = (2 * m * ν + (2 * m - 3)) + 1 := by omega
    rw [he, Gv_succ, second_coord_zero m hm ν, add_zero]

/-! ### Part 4 — the statement in the source's own sequence -/

theorem two_le_two_pow (K : ℕ) : 2 ≤ 2 ^ (K + 1) := by
  have : 2 ^ 1 ≤ 2 ^ (K + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  simpa using this

/-- **Dilcher–Ulas Conjecture 5.8 for `m = 2^{K+1}`, every block index `ν`:** the block is
strictly increasing in `(−1)^ν f` up to its last two entries, which are equal, and the final
entry of the block vanishes. -/
theorem main (K ν : ℕ) :
    0 < (-1 : ℤ) ^ ν * fsrc (K + 1) (2 * 2 ^ (K + 1) * ν)
  ∧ (∀ i, i + 3 < 2 * 2 ^ (K + 1) →
      (-1 : ℤ) ^ ν * fsrc (K + 1) (2 * 2 ^ (K + 1) * ν + i)
        < (-1 : ℤ) ^ ν * fsrc (K + 1) (2 * 2 ^ (K + 1) * ν + (i + 1)))
  ∧ fsrc (K + 1) (2 * 2 ^ (K + 1) * ν + (2 * 2 ^ (K + 1) - 3))
      = fsrc (K + 1) (2 * 2 ^ (K + 1) * ν + (2 * 2 ^ (K + 1) - 2))
  ∧ fsrc (K + 1) (2 * 2 ^ (K + 1) * ν + (2 * 2 ^ (K + 1) - 1)) = 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := block_conjecture (2 ^ (K + 1)) (two_le_two_pow K) ν
  refine ⟨?_, fun i hi => ?_, ?_, ?_⟩
  · rw [fsrc_eq]; exact h1
  · rw [fsrc_eq, fsrc_eq]; exact h2 i hi
  · rw [fsrc_eq, fsrc_eq]; exact h3
  · rw [fsrc_eq]; exact h4

end Principia.MathDB.P347788
