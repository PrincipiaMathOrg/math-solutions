import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false

/-!
# MathDB #357172 — Garcia Conjecture 6.5, the density of the quadratic-residue jumps

Write-up: `mathdb-open-problems/problems/357172/solution.tex`, collaborator branch
`mathdb-results` of `antoshashakov/Principia-Math-In-Progress` (enrolled here 2026-09-30).
Source: J. Garcia, *Class Number of the Imaginary Quadratic Field and Quadratic Residues
Identities*, arXiv:2301.02951v1, pp. 5, 22 and **Conjecture 6.5**, p. 29.

With `p = 4n−1` and `r_p(t) = t mod p`, the source sets
`Γ_n(k) = r_p((k−1)²) + r_p(k+1−3n)` and `J_n = #{k : 2 ≤ k ≤ n+2, Γ_n(k) ≥ p}`, and conjectures
`J_n/n → 3/8` through those `n` for which `4n−1` is prime. The write-up proves the limit through
**all** integers, so the prime-restricted conjecture follows.

## What is proved here, and why these pieces

The analytic core — Weyl equidistribution of `(j/p, r_p(j²)/p)` in the unit square, via a Gauss
sum bound and a Fejér-kernel approximation — is the named hypothesis `hdensity`. Everything
*around* it is exact, and all of it is proved:

* `residue_reduce` — `r_p(j+2−3n) = j+n+1` for `1 ≤ j ≤ n+1`, the write-up's opening move, which
  is what makes the second residue *linear* and turns a two-residue condition into a
  one-residue one. `n ≥ 2` is load-bearing here and the verifier exhibits the failure at `n = 1`.
* `jump_iff` — hence `Γ_n(k) ≥ p ↔ r_p(j²) + j ≥ 3n−2` with `j = k−1`: the exact defining
  inequality the lattice count uses.
* `eps_squeeze` — the write-up's "letting `ε ↓ 0`" step, `(∀ ε ∈ (0,1], L ≤ (3/2)(1/4+ε)²) →
  L ≤ 3/32`, with no analysis: `(3/2)(1/4+ε)² = 3/32 + (3/4)ε + (3/2)ε²`.
* `density_transfer` — `J_n/p → 3/32` implies `J_n/n → 3/8`, because `p/n → 4` and
  `4 · 3/32 = 3/8`. This is the last line of the write-up's proof.
* `prime_subsequence` and `prime_indices_unbounded` — **the meta-claim.** The write-up resolves a
  conjecture stated for prime `4n−1` with a theorem about all `n`, on the strength of "in
  particular". That is two separate facts, and both are proved: a limit along `atTop` restricts
  to any index map tending to `atTop`, **and** the set of `n` with `4n−1` prime is unbounded —
  which is Dirichlet's theorem on primes `≡ 3 (mod 4)`, and is exactly what stops the restricted
  conjecture from being vacuously true.

## Everything is exact integer arithmetic

`r_p` is `Int.emod`, and `J` is a `Finset.card`. The only real numbers in the file are in the
limit statements.

## What is absent

Nothing in this module is blocked on missing Mathlib. `hdensity` is unwritten, not unavailable:
Mathlib has `ZMod.gaussSum`, `Finset.sum_div_card_le`, and Fejér-kernel material, and it has
`Nat.forall_exists_prime_gt_and_eq_mod` (Dirichlet), which is used here rather than assumed.
-/

namespace Principia.MathDB.P357172

open Filter Topology

/-! ## Definitions -/

/-- `p = 4n − 1`. -/
def pp (n : ℕ) : ℕ := 4 * n - 1

/-- `r_p(t)`, the least nonnegative residue. -/
def rp (p : ℕ) (t : ℤ) : ℤ := t % (p : ℤ)

/-- `Γ_n(k) = r_p((k−1)²) + r_p(k+1−3n)`. -/
def Gamma (n : ℕ) (k : ℤ) : ℤ := rp (pp n) ((k - 1) ^ 2) + rp (pp n) (k + 1 - 3 * n)

/-- `J_n = #{k : 2 ≤ k ≤ n+2, Γ_n(k) ≥ p}`. -/
noncomputable def J (n : ℕ) : ℕ :=
  ((Finset.Icc (2 : ℤ) ((n : ℤ) + 2)).filter (fun k => (pp n : ℤ) ≤ Gamma n k)).card

/-! ## The exact arithmetic -/

theorem pp_eq (n : ℕ) (hn : 1 ≤ n) : (pp n : ℤ) = 4 * (n : ℤ) - 1 := by
  simp only [pp]
  omega

/-- **The write-up's opening move**: `r_p(j+2−3n) = j+n+1` for `1 ≤ j ≤ n+1`. This is what makes
the second residue *linear*. `n ≥ 2` is load-bearing: the bound `j+n+1 < p` needs `j < 3n−2`, and
the verifier exhibits the failure at `n = 1`. -/
theorem residue_reduce (n : ℕ) (j : ℤ) (hn : 2 ≤ n) (h1 : 1 ≤ j) (h2 : j ≤ (n : ℤ) + 1) :
    rp (pp n) (j + 2 - 3 * (n : ℤ)) = j + (n : ℤ) + 1 := by
  have hp : (pp n : ℤ) = 4 * (n : ℤ) - 1 := pp_eq n (by omega)
  have hn2 : (2 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
  have hshift : j + 2 - 3 * (n : ℤ) = (j + (n : ℤ) + 1) + (pp n : ℤ) * (-1) := by
    rw [hp]; ring
  rw [rp, hshift, Int.add_mul_emod_self_left]
  exact Int.emod_eq_of_lt (by omega) (by omega)

/-- **The exact defining inequality for a jump**, in one residue instead of two. -/
theorem jump_iff (n : ℕ) (k : ℤ) (hn : 2 ≤ n) (h1 : 2 ≤ k) (h2 : k ≤ (n : ℤ) + 2) :
    (pp n : ℤ) ≤ Gamma n k ↔ 3 * (n : ℤ) - 2 ≤ rp (pp n) ((k - 1) ^ 2) + (k - 1) := by
  have hp : (pp n : ℤ) = 4 * (n : ℤ) - 1 := pp_eq n (by omega)
  have hred : rp (pp n) (k + 1 - 3 * (n : ℤ)) = (k - 1) + (n : ℤ) + 1 := by
    have := residue_reduce n (k - 1) hn (by omega) (by omega)
    rw [show k - 1 + 2 - 3 * (n : ℤ) = k + 1 - 3 * (n : ℤ) by ring] at this
    exact this
  rw [Gamma, hred, hp]
  omega

/-! ## The `ε ↓ 0` step, with no analysis in it -/

/-- The write-up's "letting `ε ↓ 0`". `(3/2)(1/4+ε)² = 3/32 + (3/4)ε + (3/2)ε²`, so on `(0,1]`
the excess is at most `(9/4)ε`, and `le_of_forall_pos_le_add` finishes. -/
theorem eps_squeeze (L : ℝ) (h : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → L ≤ 3 / 2 * (1 / 4 + ε) ^ 2) :
    L ≤ 3 / 32 := by
  refine le_of_forall_pos_le_add ?_
  intro δ hδ
  set ε : ℝ := min 1 (4 * δ / 9) with hεdef
  have hε0 : 0 < ε := lt_min (by norm_num) (by linarith)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hεδ : ε ≤ 4 * δ / 9 := min_le_right _ _
  have := h ε hε0 hε1
  nlinarith [hε0, hε1, hεδ]

/-! ## From `J/p` to `J/n`, and the limit -/

theorem pp_div_tendsto : Tendsto (fun n : ℕ => (pp n : ℝ) / (n : ℝ)) atTop (𝓝 4) := by
  have heq : (fun n : ℕ => (pp n : ℝ) / (n : ℝ))
      =ᶠ[atTop] (fun n : ℕ => 4 - 1 / (n : ℝ)) := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    have : (pp n : ℤ) = 4 * (n : ℤ) - 1 := pp_eq n (by omega)
    have hr : (pp n : ℝ) = 4 * (n : ℝ) - 1 := by exact_mod_cast this
    rw [hr]
    field_simp
  refine Tendsto.congr' heq.symm ?_
  have : Tendsto (fun n : ℕ => (4 : ℝ) - 1 / (n : ℝ)) atTop (𝓝 (4 - 0)) :=
    tendsto_const_nhds.sub tendsto_one_div_atTop_nhds_zero_nat
  simpa using this

/-- **The write-up's last line**: `J_n/p → 3/32` gives `J_n/n → 3/8`, because `p/n → 4`. -/
theorem density_transfer
    (h : Tendsto (fun n : ℕ => (J n : ℝ) / (pp n : ℝ)) atTop (𝓝 (3 / 32))) :
    Tendsto (fun n : ℕ => (J n : ℝ) / (n : ℝ)) atTop (𝓝 (3 / 8)) := by
  have hprod := h.mul pp_div_tendsto
  have heq : (fun n : ℕ => (J n : ℝ) / (pp n : ℝ) * ((pp n : ℝ) / (n : ℝ)))
      =ᶠ[atTop] (fun n : ℕ => (J n : ℝ) / (n : ℝ)) := by
    filter_upwards [eventually_gt_atTop 1] with n hn
    have : (pp n : ℤ) = 4 * (n : ℤ) - 1 := pp_eq n (by omega)
    have hr : (pp n : ℝ) = 4 * (n : ℝ) - 1 := by exact_mod_cast this
    have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hpne : (pp n : ℝ) ≠ 0 := by rw [hr]; nlinarith
    field_simp
  refine Tendsto.congr' heq ?_
  convert hprod using 2
  norm_num

/-! ## The meta-claim: a theorem about all `n` really does settle the prime-restricted one -/

/-- Half one: a limit along `atTop` restricts to any index map tending to `atTop`. -/
theorem prime_subsequence (φ : ℕ → ℕ) (hφ : Tendsto φ atTop atTop)
    (h : Tendsto (fun n : ℕ => (J n : ℝ) / (n : ℝ)) atTop (𝓝 (3 / 8))) :
    Tendsto (fun m : ℕ => (J (φ m) : ℝ) / ((φ m : ℕ) : ℝ)) atTop (𝓝 (3 / 8)) :=
  h.comp hφ

/-- Half two, and it is the half that has content: **the set of `n` with `4n−1` prime is
unbounded**. This is Dirichlet's theorem on primes `≡ 3 (mod 4)`, and it is what stops the
source's prime-restricted conjecture from holding vacuously. -/
theorem prime_indices_unbounded (N : ℕ) : ∃ n > N, Nat.Prime (pp n) := by
  obtain ⟨q, hqgt, hqp, hqm⟩ :=
    Nat.forall_exists_prime_gt_and_eq_mod (q := 4) (a := (3 : ZMod 4))
      (by decide) (4 * N + 4)
  have hmod : q % 4 = 3 := by
    have := (ZMod.natCast_eq_natCast_iff q 3 4).1 (by rw [hqm]; rfl)
    simpa [Nat.ModEq] using this
  refine ⟨(q + 1) / 4, by omega, ?_⟩
  have : pp ((q + 1) / 4) = q := by simp only [pp]; omega
  rwa [this]

end Principia.MathDB.P357172
