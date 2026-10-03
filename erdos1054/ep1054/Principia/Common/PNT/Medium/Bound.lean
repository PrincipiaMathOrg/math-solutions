import Principia.Common.PNT.Medium.MediumPNT

set_option autoImplicit false

/-!
# The prime number theorem with classical error term, explicit for all `x ≥ 2`

`medium_PNT` is `MediumPNT` (an `isBigO` statement at `atTop`) made explicit for every `x ≥ 2`:
`|ψ(x) − x| ≤ C·x·exp(−c(log x)^{1/10})`, with the compact window `[2, X₀]` absorbed into the
constant (ψ is monotone, and the comparator is bounded below by `2·exp(−c(log M)^{1/10})`
there).

Ported **verbatim** (proof and statement unchanged, only placed in the namespace
`Principia.Common.PNT.Medium`) from "Shim 3" of the project's axiom-clean Siegel–Walfisz master
(`C:/Users/Christian/pnt/sw_full.lean`, section `SWShims`), which proved it there from PNT+'s
`MediumPNT` in the PrimeNumberTheoremAnd workspace. Here `MediumPNT` is the port in
`Principia.Common.PNT.Medium.MediumPNT`.

Its statement is, word for word, `Principia.Common.SW.MediumPNTBound`; the bridge is
`Principia.Common.SW.mediumPNTBound` in `Principia/Common/SW/Unconditional.lean`.
-/

namespace Principia.Common.PNT.Medium

open ArithmeticFunction Complex

/-- Shim 3: `medium_PNT` — the isBigO form of `MediumPNT` made explicit for all `x ≥ 2`,
    with the compact window `[2, X₀]` absorbed into the constant (ψ is monotone, and the
    comparator is bounded below by `2·exp(−c·(log M)^{1/10})` there). -/
theorem medium_PNT : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
    |(∑ n ∈ Finset.range (⌊x⌋₊ + 1), Λ n) - x|
      ≤ C * x * Real.exp (-c * Real.log x ^ ((1:ℝ)/10)) := by
  obtain ⟨c, hc, hO⟩ := MediumPNT
  rw [Asymptotics.isBigO_iff] at hO
  obtain ⟨C, hC⟩ := hO
  rw [Filter.eventually_atTop] at hC
  obtain ⟨X₀, hX₀⟩ := hC
  set M : ℝ := max 2 X₀ with hMdef
  have hM2 : (2:ℝ) ≤ M := le_max_left _ _
  have hM0 : (0:ℝ) < M := by linarith
  -- comparator lower bound on [2, M]
  set m : ℝ := 2 * Real.exp (-c * Real.log M ^ ((1:ℝ)/10)) with hmdef
  have hm0 : 0 < m := by positivity
  -- ψ is monotone in x (sum of nonnegatives over a growing range)
  have hpsi_mono : ∀ x : ℝ, x ≤ M →
      (∑ n ∈ Finset.range (⌊x⌋₊ + 1), Λ n) ≤ ∑ n ∈ Finset.range (⌊M⌋₊ + 1), Λ n := by
    intro x hx
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro k hk
      rw [Finset.mem_range] at hk ⊢
      have := Nat.floor_le_floor hx
      omega
    · intro n _ _
      exact vonMangoldt_nonneg
  set K : ℝ := (∑ n ∈ Finset.range (⌊M⌋₊ + 1), Λ n) + M with hKdef
  have hK0 : 0 < K := by
    have h1 : (0:ℝ) ≤ ∑ n ∈ Finset.range (⌊M⌋₊ + 1), Λ n :=
      Finset.sum_nonneg (fun n _ => vonMangoldt_nonneg)
    linarith
  refine ⟨c, max C 1 + K / m, hc, by positivity, ?_⟩
  intro x hx
  have hx0 : (0:ℝ) < x := by linarith
  have hcomp0 : 0 < x * Real.exp (-c * Real.log x ^ ((1:ℝ)/10)) := by positivity
  rcases le_total x M with hxM | hxM
  · -- compact window: |ψ − x| ≤ K and the comparator ≥ m·(x/x)… use m ≤ x·exp(−c logx^{1/10})
    have hψx : |(∑ n ∈ Finset.range (⌊x⌋₊ + 1), Λ n) - x| ≤ K := by
      have h1 : (0:ℝ) ≤ ∑ n ∈ Finset.range (⌊x⌋₊ + 1), Λ n :=
        Finset.sum_nonneg (fun n _ => vonMangoldt_nonneg)
      have h2 := hpsi_mono x hxM
      rw [abs_le]
      constructor
      · have : x ≤ M := hxM
        nlinarith
      · nlinarith
    have hcomp_ge : m ≤ x * Real.exp (-c * Real.log x ^ ((1:ℝ)/10)) := by
      have hlog_le : Real.log x ≤ Real.log M := Real.log_le_log hx0 hxM
      have hlx0 : (0:ℝ) ≤ Real.log x := Real.log_nonneg (by linarith)
      have hrpow_le : Real.log x ^ ((1:ℝ)/10) ≤ Real.log M ^ ((1:ℝ)/10) :=
        Real.rpow_le_rpow hlx0 hlog_le (by norm_num)
      have hexp_le : Real.exp (-c * Real.log M ^ ((1:ℝ)/10))
          ≤ Real.exp (-c * Real.log x ^ ((1:ℝ)/10)) := by
        apply Real.exp_le_exp.mpr
        nlinarith
      calc m = 2 * Real.exp (-c * Real.log M ^ ((1:ℝ)/10)) := hmdef
        _ ≤ 2 * Real.exp (-c * Real.log x ^ ((1:ℝ)/10)) := by
            apply mul_le_mul_of_nonneg_left hexp_le (by norm_num)
        _ ≤ x * Real.exp (-c * Real.log x ^ ((1:ℝ)/10)) := by
            apply mul_le_mul_of_nonneg_right hx (Real.exp_pos _).le
    calc |(∑ n ∈ Finset.range (⌊x⌋₊ + 1), Λ n) - x| ≤ K := hψx
      _ = (K / m) * m := by field_simp
      _ ≤ (K / m) * (x * Real.exp (-c * Real.log x ^ ((1:ℝ)/10))) := by
          apply mul_le_mul_of_nonneg_left hcomp_ge (by positivity)
      _ ≤ (max C 1 + K / m) * (x * Real.exp (-c * Real.log x ^ ((1:ℝ)/10))) := by
          apply mul_le_mul_of_nonneg_right _ hcomp0.le
          have : (0:ℝ) ≤ max C 1 := le_trans zero_le_one (le_max_right _ _)
          linarith
      _ = (max C 1 + K / m) * x * Real.exp (-c * Real.log x ^ ((1:ℝ)/10)) := by ring
  · -- asymptotic window: cite the isBigO bound
    have h := hX₀ x (by linarith [le_max_right (2:ℝ) X₀])
    have hψ : ChebyshevPsi x = ∑ n ∈ Finset.range (⌊x⌋₊ + 1), Λ n :=
      Chebyshev.psi_eq_sum_range x
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at h
    have hxexp : |x * Real.exp (-c * Real.log x ^ ((1:ℝ)/10))|
        = x * Real.exp (-c * Real.log x ^ ((1:ℝ)/10)) := abs_of_pos hcomp0
    calc |(∑ n ∈ Finset.range (⌊x⌋₊ + 1), Λ n) - x|
        = |(ChebyshevPsi x - x)| := by rw [hψ]
      _ ≤ C * |x * Real.exp (-c * Real.log x ^ ((1:ℝ)/10))| := by
          have := h
          simpa using this
      _ = C * (x * Real.exp (-c * Real.log x ^ ((1:ℝ)/10))) := by rw [hxexp]
      _ ≤ (max C 1 + K / m) * (x * Real.exp (-c * Real.log x ^ ((1:ℝ)/10))) := by
          apply mul_le_mul_of_nonneg_right _ hcomp0.le
          have h1 : C ≤ max C 1 := le_max_left _ _
          have h2 : (0:ℝ) ≤ K / m := by positivity
          linarith
      _ = (max C 1 + K / m) * x * Real.exp (-c * Real.log x ^ ((1:ℝ)/10)) := by ring

end Principia.Common.PNT.Medium
