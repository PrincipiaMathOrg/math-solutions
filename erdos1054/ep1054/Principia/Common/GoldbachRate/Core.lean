/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.Goldbach.Reduction

/-!
# Goldbach rate, `Core`: the circle-method variance with an explicit `1 / log N` rate

`Principia.Common.Goldbach.RatedWindow.core_variance` proves
`∑_{n<2N} ‖R(n) − coeffModel(n)‖² ≤ ε N³` for every `ε > 0` and all large `N`, at
`P = ⌊(log N)⁹⌋₊`, `Q = N/P`. Its two pieces are explicit in `N`:

* the minor arcs (`minor_L4_le_explicit`) are `≤ 46080000 N³ / log N + 4 N (log N)⁴`, the internal
  `hmain` of `minor_limit`;
* the major-arc Bessel error (`major_bessel_error_q` at `B = 9`) is
  `≤ 64 C_M N³ (log N)⁷⁴ exp(−2 c_M (log N)^{1/10})`, with `c_M, C_M` fixed (Siegel–Walfisz,
  ineffective) and independent of `ε`.

This module states them with the rate:

* `minor_rate` (R6) — the minor-arc term is `≤ 46096384 N³ / log N` for every `N ≥ 8`;
* `core_variance_rate` (R7) — `∑_{n<2N} ‖R(n) − coeffModel(n)‖² ≤ K N³ / log N`
  (`K = 46096384 + 64 C_M`), from `MediumPNTBound`;
* `core_variance_repWeight_rate` (R8) — the same in the reduction's block form,
  `∑_{n∈(X/2,X]} (repWeight X n − Re cmodel(X+1, n))² ≤ K X³ / log X`.

The proofs copy `minor_limit`, `core_variance` and `core_variance_repWeight` and replace the
`ε`-bookkeeping by a fixed `1 / log`. `major_bessel_error_q` is reused, not re-proved.
-/

set_option autoImplicit false
open DirichletCharacter Complex PowerSeries ArithmeticFunction Finset Filter Metric MeasureTheory
open Principia.Common.SW (MediumPNTBound)

namespace Principia.Common.GoldbachRate

open Principia.Common.Goldbach
open Principia.Common.Goldbach.MinSum
open Principia.Common.Goldbach.MinorArc
open Principia.Common.Goldbach.MajorArcMainTerm
open scoped ArithmeticFunction

/-- **R6 (`minor_rate`): the minor-arc term with a `1 / log N` rate.** For every `N ≥ 8`, twice
the explicit minor-L⁴ bound at `P = ⌊(log N)⁹⌋₊` is `≤ 46096384 N³ / log N`. The donor
`minor_limit`'s own algebra gives `≤ 46080000 N³ / L + 4 N L⁴` (`L = log N`), and
`4 N L⁴ ≤ 16384 N² ≤ 16384 N³ / L` from `L⁴ ≤ 4096 N` (the nested-`√` bound) and `L ≤ N`.
Rpow-free, as the donor is. -/
theorem minor_rate (N : ℕ) (hN8 : 8 ≤ N) :
    2 * (300 * (N : ℝ) * (Real.log N + 2) ^ 3 / Real.sqrt (Nat.floor ((Real.log N) ^ 9))
        + Real.log N) ^ 2 * ((N : ℝ) * Real.log N ^ 2)
      ≤ 46096384 * (N : ℝ) ^ 3 / Real.log N := by
  have hNR : (8 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN8
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  set L : ℝ := Real.log N with hLdef
  have hL2 : (2 : ℝ) ≤ L := by
    rw [hLdef]
    calc (2 : ℝ) ≤ Real.log 8 := by
          rw [show (8:ℝ) = 2^3 by norm_num, Real.log_pow]
          have h2 : (0.6931 : ℝ) ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
          push_cast; linarith
      _ ≤ Real.log N := Real.log_le_log (by norm_num) hNR
  have hLpos : (0 : ℝ) < L := by linarith
  have hLA0 : (0 : ℝ) ≤ L := le_of_lt hLpos
  set P : ℕ := Nat.floor (L ^ 9) with hPdef
  have hL9pos : (0 : ℝ) < L ^ 9 := by positivity
  have hL9ge2 : (2 : ℝ) ≤ L ^ 9 := by
    have hLL9 : L ≤ L ^ 9 := by
      calc L = L ^ 1 := (pow_one L).symm
        _ ≤ L ^ 9 := pow_le_pow_right₀ (by linarith : (1:ℝ) ≤ L) (by norm_num)
    linarith
  have hPR : (L ^ 9 / 2) ≤ (P : ℝ) := by
    have h := Nat.sub_one_lt_floor (L ^ 9)
    rw [← hPdef] at h
    have h2 : L ^ 9 - 1 ≤ (P : ℝ) := le_of_lt h
    linarith
  have hPpos : (0 : ℝ) < (P : ℝ) := by
    have : (0:ℝ) < L ^ 9 / 2 := by positivity
    linarith
  set sP : ℝ := Real.sqrt (P : ℝ) with hsPdef
  have hsPpos : (0 : ℝ) < sP := Real.sqrt_pos.mpr hPpos
  have hsPsq : sP ^ 2 = (P : ℝ) := Real.sq_sqrt (le_of_lt hPpos)
  set A : ℝ := 300 * (N : ℝ) * (L + 2) ^ 3 with hAdef
  have hA0 : (0 : ℝ) ≤ A := by rw [hAdef]; positivity
  have hL2p0 : (0:ℝ) ≤ L + 2 := by linarith
  have hL2p : (L + 2) ≤ 2 * L := by linarith
  have hL26 : (L + 2) ^ 6 ≤ 64 * L ^ 6 := by
    calc (L + 2) ^ 6 ≤ (2 * L) ^ 6 := pow_le_pow_left₀ hL2p0 hL2p 6
      _ = 64 * L ^ 6 := by ring
  have hA2val : A ^ 2 = 90000 * (N:ℝ) ^ 2 * (L + 2) ^ 6 := by rw [hAdef]; ring
  have hAsP : (A / sP) ^ 2 = A ^ 2 / (P : ℝ) := by rw [div_pow, hsPsq]
  have hTsq : (A / sP + L) ^ 2 ≤ 2 * (A ^ 2 / (P : ℝ)) + 2 * L ^ 2 := by
    nlinarith [sq_nonneg (A / sP - L), hAsP]
  have hL3pos : (0:ℝ) < L ^ 3 := by positivity
  have hfirst : 2 * (A ^ 2 / (P : ℝ)) ≤ 23040000 * (N:ℝ)^2 / L ^ 3 := by
    rw [show 2 * (A^2/(P:ℝ)) = 2*A^2/(P:ℝ) from by ring, div_le_div_iff₀ hPpos hL3pos, hA2val]
    nlinarith [mul_nonneg (sq_nonneg (N:ℝ)) (show (0:ℝ) ≤ (P:ℝ) - L^9/2 from by linarith [hPR]),
               mul_nonneg (mul_nonneg (sq_nonneg (N:ℝ)) (pow_pos hLpos 3).le)
                          (show (0:ℝ) ≤ 64*L^6 - (L+2)^6 from by linarith [hL26])]
  have hTsq2 : (A / sP + L) ^ 2 ≤ 23040000 * (N:ℝ)^2 / L ^ 3 + 2 * L ^ 2 := by
    linarith [hTsq, hfirst]
  have hmain : 2 * (A / sP + L) ^ 2 * ((N:ℝ) * L ^ 2)
      ≤ 46080000 * (N:ℝ)^3 / L + 4 * (N:ℝ) * L ^ 4 := by
    have hfac : 2 * (A / sP + L) ^ 2 * ((N:ℝ) * L ^ 2)
        ≤ 2 * (23040000 * (N:ℝ)^2 / L ^ 3 + 2 * L ^ 2) * ((N:ℝ) * L ^ 2) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_left hTsq2 (by norm_num)
    have hexp : 2 * (23040000 * (N:ℝ)^2 / L ^ 3 + 2 * L ^ 2) * ((N:ℝ) * L ^ 2)
        = 46080000 * (N:ℝ)^3 / L + 4 * (N:ℝ) * L ^ 4 := by
      field_simp
      ring
    linarith [hfac, hexp.le, hexp.ge]
  -- the second term: `L⁴ ≤ 4096 N` (nested square roots) and `L ≤ N`
  have hL4 : L ^ 4 ≤ 4096 * (N:ℝ) := by
    set s : ℝ := Real.sqrt (Real.sqrt (Real.sqrt (N:ℝ))) with hsdef
    have hLs : L ≤ 8 * s := by
      rw [hLdef, hsdef]
      have e1 : Real.log (Real.sqrt (Real.sqrt (Real.sqrt (N:ℝ)))) = Real.log N / 8 := by
        rw [Real.log_sqrt (Real.sqrt_nonneg _), Real.log_sqrt (Real.sqrt_nonneg _),
            Real.log_sqrt (le_of_lt hNpos)]; ring
      have h4 : Real.log (Real.sqrt (Real.sqrt (Real.sqrt (N:ℝ))))
          ≤ Real.sqrt (Real.sqrt (Real.sqrt (N:ℝ))) - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      rw [e1] at h4
      linarith [h4, Real.sqrt_nonneg (Real.sqrt (Real.sqrt (N:ℝ)))]
    have hs4 : s ^ 4 = Real.sqrt (N:ℝ) := by
      rw [hsdef, show (Real.sqrt (Real.sqrt (Real.sqrt (N:ℝ))))^4
            = ((Real.sqrt (Real.sqrt (Real.sqrt (N:ℝ))))^2)^2 by ring,
          Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt (Real.sqrt_nonneg _)]
    have hLpow : L ^ 4 ≤ (8 * s) ^ 4 := pow_le_pow_left₀ hLA0 hLs 4
    have hsqrtN : Real.sqrt (N:ℝ) ≤ (N:ℝ) := by
      have hle : Real.sqrt (N:ℝ) ≤ Real.sqrt ((N:ℝ)^2) := Real.sqrt_le_sqrt (by nlinarith [hNR])
      rwa [Real.sqrt_sq (le_of_lt hNpos)] at hle
    calc L ^ 4 ≤ (8 * s) ^ 4 := hLpow
      _ = 4096 * s ^ 4 := by ring
      _ = 4096 * Real.sqrt (N:ℝ) := by rw [hs4]
      _ ≤ 4096 * (N:ℝ) := by linarith [hsqrtN]
  have hLN : L ≤ (N : ℝ) := by
    have := Real.log_le_sub_one_of_pos hNpos
    linarith
  have hpart2 : 4 * (N:ℝ) * L ^ 4 ≤ 16384 * (N:ℝ) ^ 3 / L := by
    rw [le_div_iff₀ hLpos]
    calc 4 * (N:ℝ) * L ^ 4 * L ≤ 4 * (N:ℝ) * (4096 * (N:ℝ)) * (N:ℝ) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hL4 (by positivity)) hLN hLpos.le (by positivity)
      _ = 16384 * (N:ℝ) ^ 3 := by ring
  calc 2 * (A / sP + L) ^ 2 * ((N:ℝ) * L ^ 2)
      ≤ 46080000 * (N:ℝ)^3 / L + 4 * (N:ℝ) * L ^ 4 := hmain
    _ ≤ 46080000 * (N:ℝ)^3 / L + 16384 * (N:ℝ) ^ 3 / L := by linarith [hpart2]
    _ = 46096384 * (N:ℝ) ^ 3 / L := by ring

/-- **R7 (`core_variance_rate`): the circle-method variance with a `1 / log N` rate.** With
`P = ⌊(log N)⁹⌋₊`, `Q = N/P`: `∑_{n<2N} ‖R(n) − c(n)‖² ≤ K N³ / log N` for all large `N`. The
donor `core_variance` verbatim, with R6 for the minor arcs and, for the major arcs,
`exp_dominates_polylog (2 c_M) 75 1` (`(log N)⁷⁵ e^{−2 c_M (log N)^{1/10}} ≤ 1`) in place of its
`ε`-dependent instance. `major_bessel_error_q` is reused at `B = 9`. -/
theorem core_variance_rate (hPNT : MediumPNTBound) :
    ∃ K : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∑ n ∈ Finset.range (2 * N),
        ‖(∑ p ∈ (Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 = n),
            ((Λ p.1 : ℝ) : ℂ) * ((Λ p.2 : ℝ) : ℂ))
          - coeffModel N (Nat.floor ((Real.log N) ^ 9)) (N / Nat.floor ((Real.log N) ^ 9)) n‖ ^ 2
      ≤ K * (N : ℝ) ^ 3 / Real.log N := by
  obtain ⟨cM, CM, hcM, hCM, Nmaj, hmaj⟩ := major_bessel_error_q hPNT 9 (by norm_num)
  obtain ⟨Nexp, hexp⟩ := exp_dominates_polylog (2 * cM) (by linarith) 75 1 (by norm_num)
  obtain ⟨Npoly, hpoly⟩ := polylog_le_self 27 2 (by norm_num)
  refine ⟨46096384 + 64 * CM, max 8 (max Nmaj (max Nexp Npoly)), fun N hN => ?_⟩
  have hN8 : 8 ≤ N := le_trans (le_max_left _ _) hN
  have hNmaj : Nmaj ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hNexp : Nexp ≤ N :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hN
  have hNpoly : Npoly ≤ N :=
    le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hN
  -- scale facts
  have hN1 : 1 ≤ N := by omega
  have hNR : (8:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN8
  have hNpos : (0:ℝ) < (N:ℝ) := by linarith
  have hlogN2 : (2:ℝ) ≤ Real.log N := by
    calc (2:ℝ) ≤ Real.log 8 := by
          rw [show (8:ℝ) = 2^3 by norm_num, Real.log_pow]
          have := Real.log_two_gt_d9; push_cast; linarith
      _ ≤ Real.log N := Real.log_le_log (by norm_num) hNR
  have hlogNpos : (0:ℝ) < Real.log N := by linarith
  set P : ℕ := Nat.floor ((Real.log N) ^ 9) with hPdef
  set Q : ℕ := N / P with hQdef
  -- bookkeeping
  have hL9nn : (0:ℝ) ≤ (Real.log N) ^ 9 := by positivity
  have hPleL9 : (P:ℝ) ≤ (Real.log N) ^ 9 := by rw [hPdef]; exact Nat.floor_le hL9nn
  have hP2 : 2 ≤ P := by
    rw [hPdef]; apply Nat.le_floor
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hlogN2 9
    calc ((2:ℕ):ℝ) = 2 := by norm_num
      _ ≤ (2:ℝ)^9 := by norm_num
      _ ≤ (Real.log N)^9 := h
  have hP0 : 0 < P := by omega
  have hP1 : 1 ≤ P := by omega
  have hPR1 : (1:ℝ) ≤ (P:ℝ) := by exact_mod_cast hP1
  have h2poly : (2:ℝ) * (Real.log N)^27 ≤ (N:ℝ) := hpoly N hNpoly
  have hL27nn : (0:ℝ) ≤ (Real.log N)^27 := by positivity
  -- P^3 ≤ N
  have hP3R : (P:ℝ)^3 ≤ (Real.log N)^27 := by
    calc (P:ℝ)^3 ≤ ((Real.log N)^9)^3 := by apply pow_le_pow_left₀ (by positivity) hPleL9
      _ = (Real.log N)^27 := by ring
  have hP3 : P ^ 3 ≤ N := by
    have : (P:ℝ)^3 ≤ (N:ℝ) := by nlinarith [hP3R, h2poly, hL27nn]
    have h2 : ((P^3 : ℕ):ℝ) ≤ ((N:ℕ):ℝ) := by push_cast; linarith
    exact_mod_cast h2
  have hP2le : P ^ 2 ≤ N := le_trans (Nat.pow_le_pow_right hP1 (by norm_num)) hP3
  have hPN : P ≤ N := le_trans (Nat.le_self_pow (by norm_num) P) hP3
  have hQ1 : 1 ≤ Q := by rw [hQdef]; exact Nat.one_le_div_iff hP0 |>.mpr hPN
  have hPQcut : P ≤ Q := by
    rw [hQdef]; exact Nat.le_div_iff_mul_le hP0 |>.mpr (by rw [← pow_two]; exact hP2le)
  have hPmulQ : P * Q ≤ N := by rw [hQdef]; exact Nat.mul_div_le N P
  have h2P3 : 2 * P ^ 3 ≤ N := by
    have : ((2 * P^3 : ℕ):ℝ) ≤ ((N:ℕ):ℝ) := by push_cast; nlinarith [hP3R, h2poly, hL27nn]
    exact_mod_cast this
  have h2P2Q : 2 * P ^ 2 < Q + 1 := by
    have h2P2 : 2 * P ^ 2 ≤ Q := by
      rw [hQdef]; apply Nat.le_div_iff_mul_le hP0 |>.mpr
      calc 2 * P ^ 2 * P = 2 * P ^ 3 := by ring
        _ ≤ N := h2P3
    omega
  have hPB : (P:ℝ) ≤ Real.log N ^ (9:ℝ) := by
    have hbridge : Real.log N ^ (9:ℝ) = (Real.log N) ^ (9:ℕ) := by
      rw [show (9:ℝ) = ((9:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    rw [hbridge]; exact hPleL9
  -- apply variance_le_bessel
  have hbessel := variance_le_bessel (fun k => ((Λ k : ℝ) : ℂ)) N
    (Set.Ioc (0:ℝ) 1 \ MajorArcs P Q)
    (measurableSet_Ioc.diff (measurableSet_majorArcs P Q)) Set.sdiff_subset
    (coeffModel N P Q)
  -- set equality for the major integral domain
  have hset : Set.Ioc (0:ℝ) 1 \ (Set.Ioc (0:ℝ) 1 \ MajorArcs P Q)
      = ⋃ pq ∈ anchors P,
          (Metric.closedBall ((pq.2 : ℝ) / (pq.1 : ℕ)) (1 / (pq.1 * (Q + 1)))
            ∩ Set.Ioc (0:ℝ) 1) := by
    rw [Set.sdiff_sdiff_right, Set.sdiff_self, Set.empty_union, Set.inter_comm,
        majorArcs_inter_eq_anchors P Q hP0, Set.iUnion₂_inter]
  -- term1 ≤ 46096384 N³ / log N  and  term2 ≤ 64 C_M N³ / log N
  have hterm1 : 2 * (∫ α in (Set.Ioc (0:ℝ) 1 \ MajorArcs P Q),
        ‖∑ k ∈ Finset.range N, ((Λ k : ℝ) : ℂ) * e ((k : ℝ) * α)‖ ^ 4)
      ≤ 46096384 * (N:ℝ)^3 / Real.log N := by
    have hms : MeasurableSet (Set.Ioc (0:ℝ) 1 \ MajorArcs P Q) :=
      measurableSet_Ioc.diff (measurableSet_majorArcs P Q)
    have heq : (∫ α in (Set.Ioc (0:ℝ) 1 \ MajorArcs P Q),
          ‖∑ k ∈ Finset.range N, ((Λ k : ℝ) : ℂ) * e ((k : ℝ) * α)‖ ^ 4)
        = ∫ α in (Set.Ioc (0:ℝ) 1 \ MajorArcs P Q),
          ‖(∑ k ∈ Finset.range N, ((Λ k : ℝ) : ℂ) * e ((k : ℝ) * α)) ^ 2‖ ^ 2 := by
      apply MeasureTheory.setIntegral_congr_fun hms
      intro α _
      dsimp only
      rw [norm_pow]; ring
    rw [heq]
    have hL4 := minor_L4_le_explicit N P Q hP2 hP3 hPQcut hPmulQ hN1 hQ1
    have hml := minor_rate N hN8
    rw [← hPdef] at hml
    linarith [hL4, hml]
  have hterm2 : 2 * ∑ n ∈ Finset.range (2 * N),
        ‖(∫ α in Set.Ioc (0:ℝ) 1 \ (Set.Ioc (0:ℝ) 1 \ MajorArcs P Q),
            (∑ k ∈ Finset.range N, ((Λ k : ℝ) : ℂ) * e ((k : ℝ) * α)) ^ 2 * e (-((n : ℝ) * α)))
          - coeffModel N P Q n‖ ^ 2 ≤ 64 * CM * (N:ℝ)^3 / Real.log N := by
    have hsum := hmaj N hNmaj P hP0 hPB Q h2P2Q
    simp only [coeffModel]
    simp_rw [hset]
    refine le_trans (mul_le_mul_of_nonneg_left hsum (by norm_num)) ?_
    -- goal: 2 * majorRHS ≤ 64 C_M N³ / log N
    have hQ1pos : (0:ℝ) < (Q:ℝ) + 1 := by positivity
    have hNltR : (N:ℝ) < ((Q:ℝ) + 1) * P := by
      have hmod : N % P < P := Nat.mod_lt N hP0
      have hdm : P * (N / P) + N % P = N := Nat.div_add_mod N P
      have hnat : N < (Q + 1) * P := by
        have heq : (Q + 1) * P = P * (N / P) + P := by rw [hQdef]; ring
        omega
      exact_mod_cast hnat
    have hNQ : (N:ℝ) / ((Q:ℝ) + 1) ≤ (P:ℝ) := by
      rw [div_le_iff₀ hQ1pos]; nlinarith [hNltR]
    have hA : (N:ℝ) ^ 2 / ((Q:ℝ) + 1) ≤ (N:ℝ) * P := by
      rw [div_le_iff₀ hQ1pos]; nlinarith [mul_lt_mul_of_pos_left hNltR hNpos]
    have hG : (1:ℝ) + (N:ℝ) / ((Q:ℝ) + 1) ≤ 2 * P := by linarith [hNQ, hPR1]
    have hB : Real.log N + 1 ≤ 2 * Real.log N := by linarith [hlogN2]
    have hP8_72 : (P:ℝ) ^ 8 ≤ (Real.log N) ^ 72 := by
      calc (P:ℝ) ^ 8 ≤ ((Real.log N) ^ 9) ^ 8 := by
            apply pow_le_pow_left₀ (by positivity) hPleL9
        _ = (Real.log N) ^ 72 := by ring
    have hEnn : (0:ℝ) ≤ Real.exp (-(2 * cM) * Real.log N ^ ((1:ℝ) / 10)) := (Real.exp_pos _).le
    have hAnn : (0:ℝ) ≤ (N:ℝ) ^ 2 / ((Q:ℝ) + 1) := by positivity
    have hGnn : (0:ℝ) ≤ (1:ℝ) + (N:ℝ) / ((Q:ℝ) + 1) := by positivity
    have hBnn : (0:ℝ) ≤ Real.log N + 1 := by linarith [hlogNpos]
    have hmaj_ub : CM * (P:ℝ) ^ 4 * (2 * (N:ℝ)) * ((N:ℝ) ^ 2 / ((Q:ℝ) + 1)) ^ 2
          * (Real.log N + 1) ^ 2 * (1 + (N:ℝ) / ((Q:ℝ) + 1)) ^ 2
          * Real.exp (-(2 * cM) * Real.log N ^ ((1:ℝ) / 10))
        ≤ 32 * CM * (N:ℝ) ^ 3 * (Real.log N) ^ 74
          * Real.exp (-(2 * cM) * Real.log N ^ ((1:ℝ) / 10)) := by
      calc CM * (P:ℝ) ^ 4 * (2 * (N:ℝ)) * ((N:ℝ) ^ 2 / ((Q:ℝ) + 1)) ^ 2
            * (Real.log N + 1) ^ 2 * (1 + (N:ℝ) / ((Q:ℝ) + 1)) ^ 2
            * Real.exp (-(2 * cM) * Real.log N ^ ((1:ℝ) / 10))
          ≤ CM * (P:ℝ) ^ 4 * (2 * (N:ℝ)) * ((N:ℝ) * P) ^ 2
            * (2 * Real.log N) ^ 2 * (2 * (P:ℝ)) ^ 2
            * Real.exp (-(2 * cM) * Real.log N ^ ((1:ℝ) / 10)) := by
            gcongr
        _ = 32 * CM * (N:ℝ) ^ 3 * ((P:ℝ) ^ 8 * (Real.log N) ^ 2)
            * Real.exp (-(2 * cM) * Real.log N ^ ((1:ℝ) / 10)) := by ring
        _ ≤ 32 * CM * (N:ℝ) ^ 3 * ((Real.log N) ^ 72 * (Real.log N) ^ 2)
            * Real.exp (-(2 * cM) * Real.log N ^ ((1:ℝ) / 10)) := by
            apply mul_le_mul_of_nonneg_right _ hEnn
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact mul_le_mul_of_nonneg_right hP8_72 (by positivity)
        _ = 32 * CM * (N:ℝ) ^ 3 * (Real.log N) ^ 74
            * Real.exp (-(2 * cM) * Real.log N ^ ((1:ℝ) / 10)) := by ring
    have hexp' : (Real.log N) ^ 75 * Real.exp (-(2 * cM) * Real.log N ^ ((1:ℝ) / 10)) ≤ 1 :=
      hexp N hNexp
    calc 2 * (CM * (P:ℝ) ^ 4 * (2 * (N:ℝ)) * ((N:ℝ) ^ 2 / ((Q:ℝ) + 1)) ^ 2
            * (Real.log N + 1) ^ 2 * (1 + (N:ℝ) / ((Q:ℝ) + 1)) ^ 2
            * Real.exp (-(2 * cM) * Real.log N ^ ((1:ℝ) / 10)))
        ≤ 2 * (32 * CM * (N:ℝ) ^ 3 * (Real.log N) ^ 74
            * Real.exp (-(2 * cM) * Real.log N ^ ((1:ℝ) / 10))) :=
          mul_le_mul_of_nonneg_left hmaj_ub (by norm_num)
      _ ≤ 64 * CM * (N:ℝ) ^ 3 / Real.log N := by
          rw [le_div_iff₀ hlogNpos]
          calc 2 * (32 * CM * (N:ℝ) ^ 3 * (Real.log N) ^ 74
                * Real.exp (-(2 * cM) * Real.log N ^ ((1:ℝ) / 10))) * Real.log N
              = 64 * CM * (N:ℝ) ^ 3
                * ((Real.log N) ^ 75 * Real.exp (-(2 * cM) * Real.log N ^ ((1:ℝ) / 10))) := by
                ring
            _ ≤ 64 * CM * (N:ℝ) ^ 3 * 1 :=
                mul_le_mul_of_nonneg_left hexp' (by positivity)
            _ = 64 * CM * (N:ℝ) ^ 3 := by ring
  calc ∑ n ∈ Finset.range (2 * N),
        ‖(∑ p ∈ (Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 = n),
            ((Λ p.1 : ℝ) : ℂ) * ((Λ p.2 : ℝ) : ℂ)) - coeffModel N P Q n‖ ^ 2
      ≤ 2 * (∫ α in (Set.Ioc (0:ℝ) 1 \ MajorArcs P Q),
            ‖∑ k ∈ Finset.range N, ((Λ k : ℝ) : ℂ) * e ((k : ℝ) * α)‖ ^ 4)
          + 2 * ∑ n ∈ Finset.range (2 * N),
              ‖(∫ α in Set.Ioc (0:ℝ) 1 \ (Set.Ioc (0:ℝ) 1 \ MajorArcs P Q),
                  (∑ k ∈ Finset.range N, ((Λ k : ℝ) : ℂ) * e ((k : ℝ) * α)) ^ 2
                    * e (-((n : ℝ) * α)))
                - coeffModel N P Q n‖ ^ 2 := hbessel
    _ ≤ 46096384 * (N:ℝ)^3 / Real.log N + 64 * CM * (N:ℝ)^3 / Real.log N := by
        linarith [hterm1, hterm2]
    _ = (46096384 + 64 * CM) * (N:ℝ)^3 / Real.log N := by ring

/-- **R8 (`core_variance_repWeight_rate`): the variance in the reduction's block form, with a
`1 / log X` rate.** With `cmodel` the truncated model the reduction uses,
`∑_{n∈(X/2,X]} (repWeight X n − Re cmodel(X+1, n))² ≤ K X³ / log X` for all large `X`. The donor
`core_variance_repWeight` at `N = X + 1`, with `(X+1)³ / log(X+1) ≤ 8 X³ / log X`. -/
theorem core_variance_repWeight_rate (hPNT : MediumPNTBound) :
    ∃ K : ℝ, ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      ∑ n ∈ Finset.Ioc (X / 2) X,
        (GoldbachReduction.repWeight X n - (GoldbachReduction.cmodel (X + 1) n).re) ^ 2
        ≤ K * (X : ℝ) ^ 3 / Real.log X := by
  obtain ⟨K, N₀, hb⟩ := core_variance_rate hPNT
  refine ⟨8 * max K 0, max 2 N₀, fun X hX => ?_⟩
  have hX2 : 2 ≤ X := le_trans (le_max_left _ _) hX
  have hXN0 : N₀ ≤ X := le_trans (le_max_right _ _) hX
  have hX2R : (2:ℝ) ≤ (X:ℝ) := by exact_mod_cast hX2
  have hXpos : (0:ℝ) < (X:ℝ) := by linarith
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  have hXcast : ((X + 1 : ℕ) : ℝ) = (X : ℝ) + 1 := by push_cast; ring
  have hlogX1 : Real.log X ≤ Real.log ((X + 1 : ℕ) : ℝ) :=
    Real.log_le_log hXpos (by rw [hXcast]; linarith)
  have hRcast : ∀ n : ℕ,
      (∑ p ∈ (Finset.range (X + 1) ×ˢ Finset.range (X + 1)).filter (fun p => p.1 + p.2 = n),
          ((Λ p.1 : ℝ) : ℂ) * ((Λ p.2 : ℝ) : ℂ)) = ((GoldbachReduction.repWeight X n : ℝ) : ℂ) := by
    intro n
    rw [GoldbachReduction.repWeight, Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro p _
    push_cast; ring
  have hpt : ∀ (r : ℝ) (z : ℂ), (r - z.re) ^ 2 ≤ ‖(r : ℂ) - z‖ ^ 2 := by
    intro r z
    have h1 : |((r : ℂ) - z).re| ≤ ‖(r : ℂ) - z‖ := Complex.abs_re_le_norm _
    rw [Complex.sub_re, Complex.ofReal_re] at h1
    calc (r - z.re) ^ 2 = |r - z.re| ^ 2 := (sq_abs _).symm
      _ ≤ ‖(r : ℂ) - z‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
  have hbX := hb (X + 1) (by omega)
  have hsub : Finset.Ioc (X / 2) X ⊆ Finset.range (2 * (X + 1)) := by
    intro n hn
    rw [Finset.mem_Ioc] at hn
    rw [Finset.mem_range]; omega
  have hcube : ((X : ℝ) + 1) ^ 3 ≤ 8 * (X : ℝ) ^ 3 := by
    nlinarith [hX2R, mul_nonneg (mul_nonneg (show (0:ℝ) ≤ (X:ℝ) by linarith)
      (show (0:ℝ) ≤ (X:ℝ) by linarith)) (show (0:ℝ) ≤ (X:ℝ) - 1 by linarith), sq_nonneg (X:ℝ)]
  calc ∑ n ∈ Finset.Ioc (X / 2) X,
        (GoldbachReduction.repWeight X n - (GoldbachReduction.cmodel (X + 1) n).re) ^ 2
      ≤ ∑ n ∈ Finset.Ioc (X / 2) X,
          ‖(∑ p ∈ (Finset.range (X + 1) ×ˢ Finset.range (X + 1)).filter
              (fun p => p.1 + p.2 = n),
              ((Λ p.1 : ℝ) : ℂ) * ((Λ p.2 : ℝ) : ℂ)) - GoldbachReduction.cmodel (X + 1) n‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro n _
        rw [hRcast n]
        exact hpt (GoldbachReduction.repWeight X n) (GoldbachReduction.cmodel (X + 1) n)
    _ ≤ ∑ n ∈ Finset.range (2 * (X + 1)),
          ‖(∑ p ∈ (Finset.range (X + 1) ×ˢ Finset.range (X + 1)).filter
              (fun p => p.1 + p.2 = n),
              ((Λ p.1 : ℝ) : ℂ) * ((Λ p.2 : ℝ) : ℂ)) - GoldbachReduction.cmodel (X + 1) n‖ ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro n _ _; positivity
    _ ≤ K * ((X + 1 : ℕ) : ℝ) ^ 3 / Real.log ((X + 1 : ℕ) : ℝ) := hbX
    _ ≤ max K 0 * ((X + 1 : ℕ) : ℝ) ^ 3 / Real.log ((X + 1 : ℕ) : ℝ) := by
        apply div_le_div_of_nonneg_right _ (by linarith)
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    _ ≤ max K 0 * (8 * (X : ℝ) ^ 3) / Real.log X := by
        rw [hXcast]
        rw [hXcast] at hlogX1
        calc max K 0 * ((X : ℝ) + 1) ^ 3 / Real.log ((X : ℝ) + 1)
            ≤ max K 0 * (8 * (X : ℝ) ^ 3) / Real.log ((X : ℝ) + 1) := by
              apply div_le_div_of_nonneg_right _ (by linarith)
              exact mul_le_mul_of_nonneg_left hcube (le_max_right _ _)
          _ ≤ max K 0 * (8 * (X : ℝ) ^ 3) / Real.log X :=
              div_le_div_of_nonneg_left
                (mul_nonneg (le_max_right _ _) (by positivity)) hlogX hlogX1
    _ = 8 * max K 0 * (X : ℝ) ^ 3 / Real.log X := by ring

end Principia.Common.GoldbachRate
