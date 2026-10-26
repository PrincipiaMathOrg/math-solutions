import Principia.MathDB.Problem405093Q
import Principia.MathDB.Problem405093Deriv

/-!
# MathDB #405093 — unimodality and log-concavity of a lattice-path sequence

Write-up: `antoshashakov/Principia-Math-In-Progress`, branch `mathdb-results`,
`mathdb-open-problems/problems/405093/solution.tex`, proving Conjecture 6 in the problem of Martina
Juhnke (Oberwolfach Report, p. 150).  A step is `(u, 0)` or `(0, u)` with `u ≥ 1`; for `d ≥ 4`,
`N_ℓ` counts paths of `ℓ` steps from `(2, 1)` to `(d−1, d)` or to `(d, d−1)`.

**What is proved** (with `d = m + 4`, `D = 2d − 4`):
* `N_pos`, `N_zero_small`, `N_zero_large`: `N_ℓ > 0` exactly for `2 ≤ ℓ ≤ D`;
* `log_concave`: `(D−ℓ+1) N_{ℓ−1} N_{ℓ+1} ≤ (D−ℓ) N_ℓ²` for `1 ≤ ℓ < D` (the write-up's (1));
* `unimodal`: some `M` has `N` nondecreasing below `M` and nonincreasing from `M` on.

`N` is defined through the displacement: a path from `(2,1)` to `(d−1, d)` is a path from `(0,0)` to
`(d−3, d−1)` (`paths`), and to `(d, d−1)` one to `(d−2, d−2)`.

**Route (the write-up's).**  `∑ N_ℓ tˡ/ℓ! = E_{d−3}E_{d−1} + E_{d−2}² = t² Q` (`coeff_F`, `F_eq`,
from `egf_paths` and `E_a = t A_a`); `Q` has only real negative zeros (`Q_real_rooted`, from the
interlacing of the `A_a`), so `F` is real-rooted with nonnegative coefficients, and Newton's
inequalities (`newton_coeffs`) give (1).  All three statements were checked in Python for
`4 ≤ d ≤ 10`.  **Absent:** the write-up's strict form of (1) and Tasks 2 onward.
-/

namespace Principia.MathDB.P405093

open Finset Polynomial

/-- `N_ℓ` for the endpoint parameter `d`. -/
def N (d l : ℕ) : ℕ := paths (d - 3) (d - 1) l + paths (d - 2) (d - 2) l

/-- The exponential generating polynomial `E_{d−3}E_{d−1} + E_{d−2}²` at `d = m + 4`. -/
noncomputable def F (m : ℕ) : ℝ[X] :=
  E (m + 1) * E (m + 1 + 1 + 1) + E (m + 1 + 1) * E (m + 1 + 1)

theorem coeff_F (m l : ℕ) : (F m).coeff l = (N (m + 4) l : ℝ) / (l.factorial : ℝ) := by
  unfold F N
  rw [coeff_add, egf_paths, egf_paths, show m + 4 - 3 = m + 1 by omega,
    show m + 4 - 1 = m + 1 + 1 + 1 by omega, show m + 4 - 2 = m + 1 + 1 by omega]
  push_cast
  ring

theorem F_eq (m : ℕ) : F m = X ^ 2 * Q m := by
  unfold F Q
  simp only [E_eq_X_mul_A]
  ring

theorem Q_ne_zero (m : ℕ) : Q m ≠ 0 := fun h => by
  have := leadingCoeff_Q_pos m
  rw [h, leadingCoeff_zero] at this
  exact lt_irrefl 0 this

theorem natDegree_F (m : ℕ) : (F m).natDegree = 2 * m + 4 := by
  rw [F_eq, natDegree_mul (pow_ne_zero 2 X_ne_zero) (Q_ne_zero m), natDegree_X_pow, natDegree_Q]
  ring

theorem F_real_rooted (m : ℕ) : Multiset.card (F m).roots = (F m).natDegree := by
  have hne : X ^ 2 * Q m ≠ 0 := mul_ne_zero (pow_ne_zero 2 X_ne_zero) (Q_ne_zero m)
  have hQ := (Q_real_rooted m).1
  rw [natDegree_F, F_eq, roots_mul hne, roots_X_pow, Multiset.card_add, Multiset.card_nsmul,
    Multiset.card_singleton, hQ, natDegree_Q]
  ring

theorem F_coeff_nonneg (m : ℕ) : ∀ i, 0 ≤ (F m).coeff i := fun i => by
  rw [coeff_F]
  positivity

theorem factorial_mul_coeff_F (m l : ℕ) :
    (l.factorial : ℝ) * (F m).coeff l = (N (m + 4) l : ℝ) := by
  rw [coeff_F]
  have : (l.factorial : ℝ) ≠ 0 := by positivity
  field_simp

/-- **The write-up's inequality (1)**, in the non-strict form, for `1 ≤ ℓ < D`. -/
theorem log_concave (m l : ℕ) (h1 : 1 ≤ l) (h2 : l + 1 ≤ 2 * m + 4) :
    ((2 * m + 4 : ℝ) - l + 1) * ((N (m + 4) (l - 1) : ℝ) * N (m + 4) (l + 1))
      ≤ ((2 * m + 4 : ℝ) - l) * (N (m + 4) l : ℝ) ^ 2 := by
  have h := newton_coeffs (F m) (F_real_rooted m) (F_coeff_nonneg m) (l - 1)
    (by rw [natDegree_F]; omega)
  rw [factorial_mul_coeff_F, factorial_mul_coeff_F, factorial_mul_coeff_F, natDegree_F,
    show l - 1 + 2 = l + 1 by omega, show l - 1 + 1 = l by omega] at h
  push_cast [Nat.cast_sub h1] at h
  linarith

theorem N_zero_large (m l : ℕ) (hl : 2 * m + 4 < l) : N (m + 4) l = 0 := by
  have h := coeff_eq_zero_of_natDegree_lt (p := F m) (n := l) (by rw [natDegree_F]; exact hl)
  rw [coeff_F, div_eq_zero_iff] at h
  rcases h with h | h
  · exact_mod_cast h
  · exact absurd h (by positivity)

theorem N_zero_small (m l : ℕ) (hl : l < 2) : N (m + 4) l = 0 := by
  have h : (F m).coeff l = 0 := by
    rw [F_eq, coeff_X_pow_mul', if_neg (by omega)]
  rw [coeff_F, div_eq_zero_iff] at h
  rcases h with h | h
  · exact_mod_cast h
  · exact absurd h (by positivity)

theorem N_pos (m l : ℕ) (h1 : 2 ≤ l) (h2 : l ≤ 2 * m + 4) : 0 < N (m + 4) l := by
  unfold N
  rw [show m + 4 - 2 = m + 1 + 1 by omega]
  suffices hs : 0 < paths (m + 1 + 1) (m + 1 + 1) l by omega
  rw [paths_eq]
  set h := min (m + 2) (l - 1) with hh
  refine Finset.sum_pos' (fun _ _ => Nat.zero_le _) ⟨(h, l - h), ?_, ?_⟩
  · rw [mem_antidiagonal]
    omega
  · simp only
    rw [show h = (h - 1) + 1 by omega, show l - ((h - 1) + 1) = (l - h - 1) + 1 by omega,
      comp_closed, comp_closed]
    refine Nat.mul_pos (Nat.mul_pos (Nat.choose_pos (by omega)) ?_) ?_
    · exact Nat.choose_pos (by omega)
    · exact Nat.choose_pos (by omega)

/-- **Unimodality** of `ℓ ↦ N_ℓ`. -/
theorem unimodal (m : ℕ) : ∃ M, (∀ l < M, N (m + 4) l ≤ N (m + 4) (l + 1)) ∧
    ∀ l, M ≤ l → N (m + 4) (l + 1) ≤ N (m + 4) l := by
  classical
  have hex : ∃ l, N (m + 4) (l + 1) < N (m + 4) l :=
    ⟨2 * m + 4, by rw [N_zero_large m _ (by omega)]; exact N_pos m _ (by omega) le_rfl⟩
  refine ⟨Nat.find hex, fun l hl => not_lt.1 (Nat.find_min hex hl), ?_⟩
  intro l hl
  induction l, hl using Nat.le_induction with
  | base => exact (Nat.find_spec hex).le
  | succ l hMl ih =>
    by_cases hlarge : 2 * m + 4 < l + 1 + 1
    · rw [N_zero_large m _ hlarge]
      exact Nat.zero_le _
    by_cases hsmall : l + 1 < 2
    · exfalso
      have hl0 : l = 0 := by omega
      have hM0 : Nat.find hex = 0 := by omega
      have hs := Nat.find_spec hex
      rw [hM0, N_zero_small m 0 (by omega)] at hs
      exact Nat.not_lt_zero _ hs
    have hpos := N_pos m (l + 1) (by omega) (by omega)
    have hlc := log_concave m (l + 1) (by omega) (by omega)
    rw [show l + 1 - 1 = l by omega] at hlc
    have hih : (N (m + 4) (l + 1) : ℝ) ≤ N (m + 4) l := by exact_mod_cast ih
    have hp : (0 : ℝ) < N (m + 4) (l + 1) := by exact_mod_cast hpos
    have hD : (0 : ℝ) < (2 * m + 4 : ℝ) - (l + 1 : ℕ) := by
      push_cast
      have : (l : ℝ) + 1 + 1 ≤ 2 * m + 4 := by exact_mod_cast (not_lt.1 hlarge)
      linarith
    have hn0 : (0 : ℝ) ≤ N (m + 4) l := Nat.cast_nonneg _
    have hn2 : (0 : ℝ) ≤ N (m + 4) (l + 1 + 1) := Nat.cast_nonneg _
    have key : (N (m + 4) (l + 1 + 1) : ℝ) ≤ N (m + 4) (l + 1) := by
      by_contra hc
      rw [not_le] at hc
      have hX : 0 ≤ (N (m + 4) l : ℝ) * N (m + 4) (l + 1 + 1) := mul_nonneg hn0 hn2
      have h1 : (N (m + 4) l : ℝ) * N (m + 4) (l + 1 + 1) ≤ (N (m + 4) (l + 1) : ℝ) ^ 2 := by
        have hc' : ((2 * m + 4 : ℝ) - (l + 1 : ℕ)) * ((N (m + 4) l : ℝ) * N (m + 4) (l + 1 + 1))
            ≤ ((2 * m + 4 : ℝ) - (l + 1 : ℕ)) * (N (m + 4) (l + 1) : ℝ) ^ 2 := by
          nlinarith
        exact le_of_mul_le_mul_left hc' hD
      nlinarith [mul_nonneg (sub_nonneg.2 hih) hn2, mul_pos (sub_pos.2 hc) hp]
    exact_mod_cast key

end Principia.MathDB.P405093
