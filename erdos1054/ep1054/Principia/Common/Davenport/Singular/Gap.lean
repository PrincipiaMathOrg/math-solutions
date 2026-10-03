/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.Mertens.Mertens

set_option autoImplicit false

/-!
# The probability of a prime-factor gap `(t, t^v]` is at least `1/(2v)`

`gap_prod_ge`: there is `t₁` such that for all `t ≥ t₁` and `v ≥ 1`,
`∏_{t < p ≤ t^v} (1 − 1/p) ≥ 1/(2v)`.

From Mertens' third theorem in the library's form (`Mertens.prod_one_minus_div_prime_eq`,
`∏_{p ≤ x} (1 − 1/p) = e^{−γ} e^{E₃(x)} / log x` with `|E₃(x)| ≤ C / log x`, `Mertens.E₃.abs_le`):
the ratio of the two products is `(log t / log t^v) · e^{E₃(t^v) − E₃(t)} ≥ e^{−2C/log t} / v`,
and `e^{−2C/log t} ≥ 1/2` once `log t ≥ 2C / log 2`.
-/

namespace Principia.Common.Davenport.Singular

open Finset

/-- `∏_{p ≤ x} (1 − 1/p)` over the primes in `(a, b]`, split at `c`. -/
theorem prod_prime_Ioc_split (a b c : ℕ) (hab : a ≤ b) (hbc : b ≤ c) :
    (∏ p ∈ (Ioc a c).filter Nat.Prime, (1 - (1 : ℝ) / p)) =
      (∏ p ∈ (Ioc a b).filter Nat.Prime, (1 - (1 : ℝ) / p)) *
        ∏ p ∈ (Ioc b c).filter Nat.Prime, (1 - (1 : ℝ) / p) := by
  rw [Finset.prod_filter, Finset.prod_filter, Finset.prod_filter,
    Finset.prod_Ioc_consecutive _ hab hbc]

theorem prod_prime_pos (s : Finset ℕ) :
    0 < ∏ p ∈ s.filter Nat.Prime, (1 - (1 : ℝ) / p) := by
  refine Finset.prod_pos fun p hp => ?_
  have hpp := (Finset.mem_filter.1 hp).2
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
  have : (1 : ℝ) / p ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) h2
  linarith

/-- **Gap probability.** -/
theorem gap_prod_ge : ∃ t₁ : ℕ, 2 ≤ t₁ ∧ ∀ t v : ℕ, t₁ ≤ t → 1 ≤ v →
    (1 : ℝ) / (2 * v) ≤ ∏ p ∈ (Ioc t (t ^ v)).filter Nat.Prime, (1 - (1 : ℝ) / p) := by
  obtain ⟨C, hC⟩ := Mertens.E₃.abs_le
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC0 : 0 ≤ C := by
    have h := hC 2 (le_refl _)
    have h0 : 0 ≤ C / Real.log 2 := le_trans (abs_nonneg _) h
    exact (div_nonneg_iff.1 h0).elim (fun h => h.1) (fun h => absurd h.2 (not_le.2 hl2))
  refine ⟨max 2 ⌈Real.exp (2 * C / Real.log 2)⌉₊, le_max_left _ _, ?_⟩
  intro t v ht hv
  have ht2 : 2 ≤ t := le_trans (le_max_left _ _) ht
  have htR : (2 : ℝ) ≤ t := by exact_mod_cast ht2
  have hlogt : 0 < Real.log t := Real.log_pos (by linarith)
  have hvR : (1 : ℝ) ≤ v := by exact_mod_cast hv
  -- `log t ≥ 2C / log 2`
  have hlogt' : 2 * C / Real.log 2 ≤ Real.log t := by
    have h1 : Real.exp (2 * C / Real.log 2) ≤ (t : ℝ) := by
      have := le_trans (le_max_right _ _) ht
      exact le_trans (Nat.le_ceil _) (by exact_mod_cast this)
    have := Real.log_le_log (Real.exp_pos _) h1
    rwa [Real.log_exp] at this
  set T : ℕ := t ^ v with hTdef
  have hT : (T : ℝ) = (t : ℝ) ^ v := by rw [hTdef, Nat.cast_pow]
  have htT : t ≤ T := by
    rw [hTdef]
    calc t = t ^ 1 := (pow_one t).symm
      _ ≤ t ^ v := Nat.pow_le_pow_right (by omega) hv
  have hTR : (t : ℝ) ≤ T := by exact_mod_cast htT
  have hlogT : Real.log (T : ℝ) = v * Real.log t := by rw [hT, Real.log_pow]
  -- Mertens 3 at `t` and at `T`
  have hMt := Mertens.prod_one_minus_div_prime_eq (x := (t : ℝ)) (by linarith)
  have hMT := Mertens.prod_one_minus_div_prime_eq (x := (T : ℝ)) (by linarith)
  rw [Nat.floor_natCast] at hMt hMT
  have hsplit := prod_prime_Ioc_split 0 t T (Nat.zero_le t) htT
  -- the error terms
  have hEt := hC t htR
  have hET := hC T (by linarith)
  have hlogTt : Real.log t ≤ Real.log T := Real.log_le_log (by linarith) hTR
  have hCT : C / Real.log T ≤ C / Real.log t := div_le_div_of_nonneg_left hC0 hlogt hlogTt
  have hdiff : Mertens.E₃ t - Real.log 2 ≤ Mertens.E₃ T := by
    have a1 := (abs_le.1 hEt).2
    have a2 := (abs_le.1 hET).1
    have h2C : 2 * C / Real.log t ≤ Real.log 2 := by
      rw [div_le_iff₀ hlogt]
      rw [div_le_iff₀ hl2] at hlogt'
      linarith
    have : 2 * C / Real.log t = C / Real.log t + C / Real.log t := by ring
    linarith
  have hexp : Real.exp (Mertens.E₃ t) / 2 ≤ Real.exp (Mertens.E₃ T) := by
    have := Real.exp_le_exp.2 hdiff
    rw [Real.exp_sub, Real.exp_log (by norm_num)] at this
    exact this
  -- compare `Pf t / (2v)` with `Pf T`
  set Pt := ∏ p ∈ (Ioc 0 t).filter Nat.Prime, (1 - (1 : ℝ) / p) with hPt
  set W := ∏ p ∈ (Ioc t T).filter Nat.Prime, (1 - (1 : ℝ) / p) with hW
  have hPtpos : 0 < Pt := prod_prime_pos _
  have hfilt : ∀ x : ℕ, (Ioc 0 x).filter Nat.Prime = {p ∈ Ioc 0 x | p.Prime} := fun x => rfl
  have hPt' :
      Pt = Real.exp (-Real.eulerMascheroniConstant) * Real.exp (Mertens.E₃ t) / Real.log t :=
    hMt
  have hPT' : Pt * W =
      Real.exp (-Real.eulerMascheroniConstant) * Real.exp (Mertens.E₃ T) / Real.log T := by
    rw [← hsplit]
    exact hMT
  have key : Pt * (1 / (2 * v)) ≤ Pt * W := by
    rw [hPT', hPt', hlogT]
    have hA : 0 < Real.exp (-Real.eulerMascheroniConstant) := Real.exp_pos _
    have hv0 : (0 : ℝ) < v := by linarith
    rw [show Real.exp (-Real.eulerMascheroniConstant) * Real.exp (Mertens.E₃ t) / Real.log t *
        (1 / (2 * v)) = Real.exp (-Real.eulerMascheroniConstant) / (v * Real.log t) *
          (Real.exp (Mertens.E₃ t) / 2) by field_simp,
      show Real.exp (-Real.eulerMascheroniConstant) * Real.exp (Mertens.E₃ T) / (v * Real.log t) =
        Real.exp (-Real.eulerMascheroniConstant) / (v * Real.log t) *
          Real.exp (Mertens.E₃ T) by ring]
    exact mul_le_mul_of_nonneg_left hexp (by positivity)
  exact le_of_mul_le_mul_left key hPtpos

end Principia.Common.Davenport.Singular
