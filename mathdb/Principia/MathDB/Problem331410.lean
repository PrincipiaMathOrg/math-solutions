/-
MathDB #331410 — prime periods of the chocolate numbers.

Same paper and same `B_n` as `Problem331409.lean` (Conjecture 16); this is **Conjecture 23**
(Conjecture 3 of the preprint), which asks for an eventual period divisible by `p(p−1)` for the
primes with `p ≠ 2, 5` and `p ≢ ±1 (mod 5)` — exactly the primes for which **5 is a quadratic
nonresidue**, which is the complementary half of the dichotomy #331409 proves.

The write-up identifies `p(p−1)` itself as a period, via a sharper *half*-shift: with
`T = p(p−1)/2` and `ε = (−5/p) ∈ {1, −1}`,

    B_{n+T} ≡ ε · B_n  (mod p)   for every n ≥ (p+1)/2,

and then says "consequently `B_{n+p(p−1)} ≡ B_n`".

WHAT IS PROVED HERE.  **That "consequently" is proved rather than restated** — `full_period`
derives the `2T` period from the half-shift and `ε² = 1` by applying the shift twice, and
`two_mul_T` supplies `2T = p(p−1)` (the product of consecutive integers is even).  Also proved:
`eps_sq_one`; `nonresidue_iff`, which **reuses #331409's `five_sq_iff` by import** to turn the
residue condition into the source's congruence `p ≡ ±2 (mod 5)`; and `T_three`, the write-up's
own sanity check that at `p = 3` the formula gives `T = 3`, recovering the period-3 result the
source already proves, from index `(p+1)/2 = 2`.

CARRIED.  `HalfShift` itself is a named hypothesis.  Proving it is the write-up's real work and
needs `ℱ_{p²}`: iterating the `d` recurrence `p` times gives
`∏_{r ∈ 𝔽_p} (r² − r − 1) = (α^p − α)(β^p − β) = −(α − β)² = −5` for the roots `α, β` of
`X² − X − 1`, whence `δ²U = −5U` for `δ = D^p`, and `L = D^{p²} − ε D^p` is a derivation killing
`U`.  None of that is in reach here, and per the spine rule it is a hypothesis, never a `sorry`.

The theorem specifies *a* period and does not claim it is least — the file states it that way.
-/
import Principia.MathDB.Problem331409

set_option autoImplicit false

namespace Principia.MathDB.P331410

open Principia.MathDB

/-! ## 1. The shift parameter -/

/-- `T = p(p−1)/2`, the half-period. -/
def T (p : ℕ) : ℕ := p * (p - 1) / 2

/-- `2T = p(p−1)`: the product of consecutive integers is even. -/
theorem two_mul_T (p : ℕ) (hp : 1 ≤ p) : 2 * T p = p * (p - 1) := by
  have he : Even ((p - 1) * ((p - 1) + 1)) := Nat.even_mul_succ_self _
  have hsucc : (p - 1) + 1 = p := Nat.succ_pred_eq_of_pos hp
  rw [hsucc] at he
  have hcomm : (p - 1) * p = p * (p - 1) := Nat.mul_comm _ _
  rw [hcomm] at he
  obtain ⟨k, hk⟩ := he
  rw [T, hk]
  omega

/-- The write-up's own sanity check: at `p = 3` the formula gives `T = 3`, which is the period
the source already proves, valid from index `(p+1)/2 = 2`. -/
theorem T_three : T 3 = 3 ∧ (3 + 1) / 2 = 2 := by decide

/-! ## 2. `ε = ±1` -/

/-- `ε² = 1` for `ε = ±1`.  This is what makes the half-shift square to a genuine period. -/
theorem eps_sq_one {eps : ℤ} (h : eps = 1 ∨ eps = -1) : eps * eps = 1 := by
  rcases h with h | h <;> rw [h] <;> ring

/-! ## 3. The half-shift, and the period it forces -/

/-- The write-up's Theorem: `B_{n+T} ≡ ε B_n (mod p)` from index `(p+1)/2` on.  Carried as a
hypothesis — proving it needs the `𝔽_{p²}` argument described in the header. -/
def HalfShift (B : ℕ → ℤ) (p T : ℕ) (eps : ℤ) : Prop :=
  ∀ n, (p + 1) / 2 ≤ n → B (n + T) ≡ eps * B n [ZMOD (p : ℤ)]

/-- **The "consequently", proved.**  Applying the half-shift twice and using `ε² = 1` turns a
sign-twisted half-shift into an honest period of `2T`. -/
theorem full_period (B : ℕ → ℤ) (p Tp : ℕ) (eps : ℤ) (heps : eps * eps = 1)
    (h : HalfShift B p Tp eps) (n : ℕ) (hn : (p + 1) / 2 ≤ n) :
    B (n + 2 * Tp) ≡ B n [ZMOD (p : ℤ)] := by
  have h1 : B (n + Tp) ≡ eps * B n [ZMOD (p : ℤ)] := h n hn
  have hn2 : (p + 1) / 2 ≤ n + Tp := le_trans hn (Nat.le_add_right _ _)
  have h2 : B (n + Tp + Tp) ≡ eps * B (n + Tp) [ZMOD (p : ℤ)] := h (n + Tp) hn2
  have h3 : eps * B (n + Tp) ≡ eps * (eps * B n) [ZMOD (p : ℤ)] := h1.mul_left eps
  have h4 : eps * (eps * B n) = B n := by
    rw [← mul_assoc, heps, one_mul]
  have hidx : n + Tp + Tp = n + 2 * Tp := by ring
  rw [hidx] at h2
  rw [h4] at h3
  exact h2.trans h3

/-! ## 4. The dichotomy, reused from #331409 by import -/

/-- `5` is a NONresidue mod `p` exactly when `p ≡ ±2 (mod 5)` — the complementary half of
#331409's `five_sq_iff`, and the class this row's conjecture is about. -/
theorem nonresidue_iff (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hp5 : p ≠ 5) :
    ¬ IsSquare (5 : ZMod p) ↔ (p % 5 = 2 ∨ p % 5 = 3) := by
  rw [P331409.five_sq_iff p hp2 hp5]
  have hlt : p % 5 < 5 := Nat.mod_lt _ (by norm_num)
  have hp0 : p % 5 ≠ 0 := by
    intro h
    rcases (Fact.out : p.Prime).eq_one_or_self_of_dvd 5 (Nat.dvd_of_mod_eq_zero h) with h1 | h1
    · norm_num at h1
    · exact hp5 h1.symm
  omega

/-! ## 5. Conjecture 23 -/

/-- **Conjecture 23**: for every prime outside the `±1 (mod 5)` class, `p(p−1)` is an eventual
period of the chocolate numbers mod `p`.  The statement asserts *a* period, not the least one. -/
def Conjecture23 (B : ℕ → ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 5 → (p % 5 = 2 ∨ p % 5 = 3) →
    ∀ n, (p + 1) / 2 ≤ n → B (n + p * (p - 1)) ≡ B n [ZMOD (p : ℤ)]

/-- Conjecture 23 follows from the half-shift family, with no further input: this is the
composition `full_period` + `two_mul_T`, so the only obligation left is `HalfShift` itself. -/
theorem conjecture23_of_halfShift (B : ℕ → ℤ)
    (hs : ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 5 → (p % 5 = 2 ∨ p % 5 = 3) →
      ∃ eps : ℤ, (eps = 1 ∨ eps = -1) ∧ HalfShift B p (T p) eps) :
    Conjecture23 B := by
  intro p hp hp2 hp5 hclass n hn
  obtain ⟨eps, heps, hhalf⟩ := hs p hp hp2 hp5 hclass
  have h := full_period B p (T p) eps (eps_sq_one heps) hhalf n hn
  rwa [two_mul_T p hp.pos] at h

end Principia.MathDB.P331410
