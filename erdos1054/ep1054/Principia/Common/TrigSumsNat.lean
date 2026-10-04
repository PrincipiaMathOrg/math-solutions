/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TrigSums

set_option autoImplicit false

/-!
# The trigonometric-sum lemmas on natural windows, and window bookkeeping

`Common.TrigSums` states `lem:gotog`, `lem:couscous`, `lem:thina` (Helfgott, `typeI.tex`) for
functions on `ℤ` summed over integer intervals. The Type I sums of the minor arcs (`eq:esthel`,
`eq:esthel2`, `eq:esthel3`) sum over natural `m`. This module provides:

* `gotogN`, `couscousN`, `thinaN` -- the three lemmas over natural intervals (pure transport);
* `sum_windows`, `window_trunc`, `sum_filter_windows` -- cutting `(h, N]` into windows of
  length `q` (the `∑_j ∑_{jq < m ≤ (j+1)q}` of the book), with the tail truncated at `N`;
* `harm_le` -- `∑_{j < J} 1/((j+1)q + R) ≤ (1/q) log((Jq + R)/R)`, the book's
  `∑_j 1/(jq + R) ≤ 1/R + (1/q)∫_R^D dt/t` (`eq:tenda`, `eq:kosto`) without integrals
  (from `log y ≥ 1 - 1/y`, telescoped).

Nothing here mentions a campaign object.
-/

namespace Principia.Common.TrigSumN

open Real Finset Principia.Common.TrigSum

/-- A sum over a natural `Ioc` is the same sum over the integer `Ioc`. -/
theorem sum_Ioc_int (f : ℕ → ℝ) (a b : ℕ) :
    ∑ n ∈ Ioc a b, f n = ∑ z ∈ Ioc (a : ℤ) b, f z.toNat := by
  refine Finset.sum_nbij' (fun n => (n : ℤ)) (fun z => z.toNat) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    simp only [Finset.mem_Ioc] at hn ⊢
    omega
  · intro z hz
    simp only [Finset.mem_Ioc] at hz ⊢
    omega
  · intro n _
    simp
  · intro z hz
    simp only [Finset.mem_Ioc] at hz
    omega
  · intro n _
    simp

/-- The same with a filter. -/
theorem sum_Ioc_int_filter (f : ℕ → ℝ) (a b q : ℕ) :
    ∑ n ∈ (Ioc a b).filter (fun n => ¬ q ∣ n), f n =
      ∑ z ∈ (Ioc (a : ℤ) b).filter (fun z => ¬ (q : ℤ) ∣ z), f z.toNat := by
  rw [Finset.sum_filter, Finset.sum_filter, sum_Ioc_int]
  refine Finset.sum_congr rfl fun z hz => ?_
  have hz0 : 0 ≤ z := by
    have := (Finset.mem_Ioc.mp hz).1
    omega
  have e : ((z.toNat : ℕ) : ℤ) = z := Int.toNat_of_nonneg hz0
  have hd : (q ∣ z.toNat) ↔ ((q : ℤ) ∣ z) := by
    rw [← Int.natCast_dvd_natCast, e]
  simp only [hd]

/-- **T1 (`lem:gotog`) on a natural window `(n₀, n₀ + q]`.** -/
theorem gotogN (α β Q A C : ℝ) (a : ℤ) (q : ℕ) (hq : 1 ≤ q) (hcop : Int.gcd a q = 1)
    (hα : α = a / q + β / (q * Q)) (hβ : |β| ≤ 1) (hqQ : (q : ℝ) ≤ Q) (hA : 0 ≤ A)
    (hC : 0 ≤ C) (n0 : ℕ) (t : ℕ → ℝ) (htA : ∀ n ∈ Ioc n0 (n0 + q), t n ≤ A)
    (htC : ∀ n ∈ Ioc n0 (n0 + q), t n * sin (π * (α * n)) ^ 2 ≤ C) :
    ∑ n ∈ Ioc n0 (n0 + q), t n ≤ 3 * A + 4 * q / π * √(A * C) := by
  rw [sum_Ioc_int]
  have e : ((n0 + q : ℕ) : ℤ) = (n0 : ℤ) + q := by push_cast; ring
  rw [e]
  refine gotog α β Q A C a q hq hcop hα hβ hqQ hA hC n0 (fun z => t z.toNat) ?_ ?_
  · intro z hz
    have hz' : z.toNat ∈ Ioc n0 (n0 + q) := by
      simp only [Finset.mem_Ioc] at hz ⊢
      omega
    exact htA _ hz'
  · intro z hz
    have hz0 : 0 ≤ z := by
      have := (Finset.mem_Ioc.mp hz).1
      omega
    have hz' : z.toNat ∈ Ioc n0 (n0 + q) := by
      simp only [Finset.mem_Ioc] at hz ⊢
      omega
    have hc : ((z.toNat : ℕ) : ℝ) = (z : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hz0
    have := htC _ hz'
    rw [hc] at this
    exact this

/-- **T2 (`lem:couscous`) on a natural window `(n₁, n₂]`.** -/
theorem couscousN (α β Q C : ℝ) (a : ℤ) (q : ℕ) (hq : 1 ≤ q) (hcop : Int.gcd a q = 1)
    (hα : α = a / q + β / (q * Q)) (hβ : |β| ≤ 1) (hC : 0 ≤ C) (n1 n2 : ℕ)
    (hn12 : n2 ≤ n1 + q) (hn2 : (n2 : ℝ) ≤ Q / 2) (t : ℕ → ℝ)
    (htC : ∀ n ∈ (Ioc n1 n2).filter (fun n => ¬ q ∣ n), t n * sin (π * (α * n)) ^ 2 ≤ C) :
    ∑ n ∈ (Ioc n1 n2).filter (fun n => ¬ q ∣ n), t n ≤ 20 / (3 * π ^ 2) * C * q ^ 2 := by
  rw [sum_Ioc_int_filter]
  refine couscous α β Q C a q hq hcop hα hβ hC n1 n2 (by positivity) (by omega)
    (by exact_mod_cast hn2) (fun z => t z.toNat) ?_
  intro z hz
  have hz0 : 0 ≤ z := by
    have := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hz).1).1
    omega
  have e : ((z.toNat : ℕ) : ℤ) = z := Int.toNat_of_nonneg hz0
  have hz' : z.toNat ∈ (Ioc n1 n2).filter (fun n => ¬ q ∣ n) := by
    rw [Finset.mem_filter, Finset.mem_Ioc] at hz ⊢
    refine ⟨by omega, ?_⟩
    rw [← Int.natCast_dvd_natCast, e]
    exact hz.2
  have hc : ((z.toNat : ℕ) : ℝ) = (z : ℝ) := by exact_mod_cast e
  have := htC _ hz'
  rw [hc] at this
  exact this

/-- **T3 (`lem:thina`) on a natural window `(n₁, n₂]`.** -/
theorem thinaN (α β Q B C : ℝ) (a : ℤ) (q : ℕ) (hq : 1 ≤ q) (hcop : Int.gcd a q = 1)
    (hα : α = a / q + β / (q * Q)) (hβ : |β| ≤ 1) (hB : 0 ≤ B) (hC : 0 ≤ C) (n1 n2 : ℕ)
    (hn12 : n2 ≤ n1 + q) (hn2 : (n2 : ℝ) ≤ Q / 2) (t : ℕ → ℝ)
    (htB : ∀ n ∈ (Ioc n1 n2).filter (fun n => ¬ q ∣ n), t n * |sin (π * (α * n))| ≤ B)
    (htC : ∀ n ∈ (Ioc n1 n2).filter (fun n => ¬ q ∣ n), t n * sin (π * (α * n)) ^ 2 ≤ C) :
    ∑ n ∈ (Ioc n1 n2).filter (fun n => ¬ q ∣ n), t n ≤
      2 * B * q / π * max 2 (log (C * exp 3 * q / (B * π))) := by
  rw [sum_Ioc_int_filter]
  have key : ∀ z ∈ (Ioc (n1 : ℤ) n2).filter (fun z => ¬ (q : ℤ) ∣ z),
      z.toNat ∈ (Ioc n1 n2).filter (fun n => ¬ q ∣ n) ∧ ((z.toNat : ℕ) : ℝ) = (z : ℝ) := by
    intro z hz
    have hz0 : 0 ≤ z := by
      have := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hz).1).1
      omega
    have e : ((z.toNat : ℕ) : ℤ) = z := Int.toNat_of_nonneg hz0
    refine ⟨?_, by exact_mod_cast e⟩
    rw [Finset.mem_filter, Finset.mem_Ioc] at hz ⊢
    refine ⟨by omega, ?_⟩
    rw [← Int.natCast_dvd_natCast, e]
    exact hz.2
  refine thina α β Q B C a q hq hcop hα hβ hB hC n1 n2 (by positivity) (by omega)
    (by exact_mod_cast hn2) (fun z => t z.toNat) ?_ ?_
  · intro z hz
    obtain ⟨h1, h2⟩ := key z hz
    have := htB _ h1
    rw [h2] at this
    exact this
  · intro z hz
    obtain ⟨h1, h2⟩ := key z hz
    have := htC _ h1
    rw [h2] at this
    exact this

/-- **Windows**: `(h, h + Jq]` is the union of the `J` windows `(h + jq, h + jq + q]`. -/
theorem sum_windows (t : ℕ → ℝ) (h q J : ℕ) :
    ∑ d ∈ Ioc h (h + J * q), t d =
      ∑ j ∈ range J, ∑ d ∈ Ioc (h + j * q) (h + j * q + q), t d := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_range_succ, ← ih]
    have e : h + (J + 1) * q = h + J * q + q := by ring
    rw [e, Finset.sum_Ioc_consecutive _ (by omega) (by omega)]

/-- The truncation `t·1_{d ≤ N, P d}` summed over a window is the filtered sum up to `N`. -/
theorem window_trunc (t : ℕ → ℝ) (P : ℕ → Prop) [DecidablePred P] (n1 L N : ℕ) :
    ∑ d ∈ Ioc n1 (n1 + L), (if d ≤ N ∧ P d then t d else 0) =
      ∑ d ∈ (Ioc n1 (min (n1 + L) N)).filter P, t d := by
  rw [Finset.sum_filter]
  have h1 : ∑ d ∈ Ioc n1 (min (n1 + L) N), (if P d then t d else 0) =
      ∑ d ∈ Ioc n1 (min (n1 + L) N), (if d ≤ N ∧ P d then t d else 0) := by
    refine Finset.sum_congr rfl fun d hd => ?_
    have hdN : d ≤ N := by
      have := (Finset.mem_Ioc.mp hd).2
      omega
    simp only [hdN, true_and]
  rw [h1]
  symm
  refine Finset.sum_subset ?_ ?_
  · intro d hd
    rw [Finset.mem_Ioc] at hd ⊢
    omega
  · intro d hd hnd
    have hN : ¬ d ≤ N := by
      intro hle
      apply hnd
      rw [Finset.mem_Ioc] at hd ⊢
      omega
    simp only [hN, false_and, if_false]

/-- **Windowed bound**: for `t ≥ 0` and `N ≤ h + Jq`, the filtered sum over `(h, N]` is the sum of
the truncated window sums. -/
theorem sum_filter_windows (t : ℕ → ℝ) (P : ℕ → Prop) [DecidablePred P] (h q J N : ℕ)
    (hN : N ≤ h + J * q) :
    ∑ d ∈ (Ioc h N).filter P, t d =
      ∑ j ∈ range J, ∑ d ∈ Ioc (h + j * q) (h + j * q + q),
        (if d ≤ N ∧ P d then t d else 0) := by
  rw [← sum_windows, Finset.sum_filter]
  refine Finset.sum_subset_zero_on_sdiff ?_ ?_ ?_
  · intro d hd
    rw [Finset.mem_Ioc] at hd ⊢
    omega
  · intro d hd
    rw [Finset.mem_sdiff, Finset.mem_Ioc, Finset.mem_Ioc] at hd
    have hN' : ¬ d ≤ N := by omega
    simp only [hN', false_and, if_false]
  · intro d hd
    have hdN : d ≤ N := (Finset.mem_Ioc.mp hd).2
    simp only [hdN, true_and]

/-- **The harmonic sum along an arithmetic progression**: `∑_{j < J} 1/((j+1)q + R) ≤
(1/q)·log((Jq + R)/R)`. -/
theorem harm_le (q R : ℝ) (hq : 0 < q) (hR : 0 < R) (J : ℕ) :
    ∑ j ∈ range J, 1 / (((j : ℝ) + 1) * q + R) ≤ 1 / q * Real.log ((J * q + R) / R) := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_range_succ]
    have hJ0 : (0 : ℝ) ≤ J := Nat.cast_nonneg J
    have hA : 0 < (J : ℝ) * q + R := by positivity
    have hB : 0 < ((J : ℝ) + 1) * q + R := by positivity
    have hlog : Real.log ((((J + 1 : ℕ) : ℝ) * q + R) / R) =
        Real.log (((J : ℝ) * q + R) / R) + Real.log ((((J : ℝ) + 1) * q + R) / (J * q + R)) := by
      rw [← Real.log_mul (by positivity) (by positivity)]
      congr 1
      push_cast
      field_simp
    have hstep : 1 / (((J : ℝ) + 1) * q + R) ≤
        1 / q * Real.log ((((J : ℝ) + 1) * q + R) / (J * q + R)) := by
      have h1 := Real.one_sub_inv_le_log_of_pos (x := (((J : ℝ) + 1) * q + R) / (J * q + R))
        (by positivity)
      have e : 1 - ((((J : ℝ) + 1) * q + R) / (J * q + R))⁻¹ = q / (((J : ℝ) + 1) * q + R) := by
        field_simp
        ring
      rw [e] at h1
      rw [div_le_iff₀ hB]
      have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 1 / q)
      have e2 : 1 / q * (q / (((J : ℝ) + 1) * q + R)) = 1 / (((J : ℝ) + 1) * q + R) := by
        field_simp
      rw [e2] at this
      calc (1 : ℝ) = 1 / (((J : ℝ) + 1) * q + R) * (((J : ℝ) + 1) * q + R) := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_right this hB.le
    rw [hlog, mul_add]
    linarith

end Principia.Common.TrigSumN
