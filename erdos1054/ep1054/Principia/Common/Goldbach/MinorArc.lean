/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.Goldbach.Vaughan

/-!
# Almost-all binary Goldbach, `MinorArc`: the `minorCsup` asymptotic, additive-character orthogonality, Parseval

Ported **verbatim** from the circle-method half of the comparator-certified master
`GoldbachChainMaster.lean` (PNT+ workspace, lines 19847–21551; there
`#print axioms GoldbachChain.GoldbachReduction.almost_all_binary_goldbach_proven =
[propext, Classical.choice, Quot.sound]`, built on Mathlib `db127794`, one day from ours). The
master's lines 1–15806 are the Siegel–Walfisz master, ported separately as `Principia.Common.SW`
and not duplicated here. The master imported `Mathlib` and two PNT+ modules; here the imports are
narrowed, the namespace `GoldbachChain` is `Principia.Common.Goldbach`, and the one Siegel–Walfisz
input carries the SW port's hypothesis `MediumPNTBound` (see `Principia.Common.Goldbach.Reduction`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
open DirichletCharacter Complex PowerSeries ArithmeticFunction Finset Filter Metric MeasureTheory

namespace Principia.Common.Goldbach
set_option maxHeartbeats 1000000
open Finset


open MinSum

set_option maxHeartbeats 4000000
/-!
# The minor-arc `minorCsup` asymptotic bound (Phase D — minor smallness)

`minorCsup_bound`: for `U=V=P` with `P^3 <= N` and `P*Q <= N`,
  `minorCsup N P P P Q <= 300 * N * (log N + 2)^3 / sqrt P`.
The `N * polylog / sqrt P` bound that closes the minor L4 smallness once `P = (log N)^B`,
`B >= 8`. Heavy to elaborate (~576s) so kept in its OWN file; imported into
`MinorArcExpSum.lean` as the labeled axiom `minorCsup_bound` (discharged at Phase-F concat;
the `minorCsup` def here is duplicated verbatim, defeq to MinorArcExpSum's).
Pinned leanprover/lean4:v4.31.0.
-/
open Finset
namespace MinorArc


/-- `Nat.log 2 N ≤ 2·log N`. -/
lemma natlog2_le_two_log (N : ℕ) (hN : 2 ≤ N) : ((Nat.log 2 N : ℕ) : ℝ) ≤ 2 * Real.log N := by
  have hself : (2 : ℕ) ^ Nat.log 2 N ≤ N := Nat.pow_log_le_self 2 (by omega)
  have hlog : ((Nat.log 2 N : ℝ)) * Real.log 2 ≤ Real.log N := by
    have h1 : Real.log ((2 : ℝ) ^ Nat.log 2 N) ≤ Real.log N :=
      Real.log_le_log (by positivity) (by exact_mod_cast hself)
    rwa [Real.log_pow] at h1
  have hlog2 : (1 : ℝ) / 2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hk0 : (0:ℝ) ≤ ((Nat.log 2 N : ℕ) : ℝ) := by positivity
  nlinarith [hlog, hlog2, hk0, mul_nonneg hk0 (show (0:ℝ) ≤ Real.log 2 - 1/2 by linarith)]

-- abstract group bounds (over abstract reals — light to elaborate, instantiated below)
lemma csup_g1 (a b c d p q Z L : ℝ)
    (ha : a ≤ L) (ha0 : 0 ≤ a) (hb : b ≤ 2 * Z) (hc : 1 + c ≤ L) (hc0 : 0 ≤ 1 + c)
    (hpq : 16 * p + 4 * q ≤ 20 * Z) (hd : 2 + d ≤ 2 * L) (hd0 : 0 ≤ 2 + d) (hp : p ≤ Z * L)
    (hZ0 : 0 ≤ Z) (hL1 : 1 ≤ L) :
    2 * a * (b * (1 + c) + (16 * p + 4 * q) * (2 + d) + p) ≤ 90 * (Z * L ^ 3) := by
  have hA : b * (1 + c) ≤ 2 * (Z * L) := by
    calc b * (1 + c) ≤ (2 * Z) * L := mul_le_mul hb hc hc0 (by linarith)
      _ = 2 * (Z * L) := by ring
  have hBb : (16 * p + 4 * q) * (2 + d) ≤ 40 * (Z * L) := by
    calc (16 * p + 4 * q) * (2 + d) ≤ (20 * Z) * (2 * L) := mul_le_mul hpq hd hd0 (by linarith)
      _ = 40 * (Z * L) := by ring
  have hin : b * (1 + c) + (16 * p + 4 * q) * (2 + d) + p ≤ 43 * (Z * L) := by
    nlinarith [hA, hBb, hp]
  calc 2 * a * (b * (1 + c) + (16 * p + 4 * q) * (2 + d) + p)
      ≤ 2 * a * (43 * (Z * L)) := by apply mul_le_mul_of_nonneg_left hin (by linarith)
    _ ≤ (2 * L) * (43 * (Z * L)) := by apply mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = 86 * (Z * L ^ 2) := by ring
    _ ≤ 90 * (Z * L ^ 3) := by
        nlinarith [mul_nonneg (mul_nonneg hZ0 (sq_nonneg L)) (show (0:ℝ) ≤ 90 * L - 86 by linarith)]

lemma csup_g2 (b cc d p q Z L : ℝ)
    (hf : cc ≤ 2 * L) (hf0 : 0 ≤ cc) (hb : b ≤ 2 * Z) (hc : 1 + cc ≤ 2 * L) (hc0 : 0 ≤ 1 + cc)
    (hpq : 16 * (p * p) + 4 * q ≤ 20 * Z) (hd : 2 + d ≤ 2 * L) (hd0 : 0 ≤ 2 + d)
    (hZ0 : 0 ≤ Z) (hL1 : 1 ≤ L) :
    cc * (b * (1 + cc) + (16 * (p * p) + 4 * q) * (2 + d)) ≤ 90 * (Z * L ^ 3) := by
  have hA : b * (1 + cc) ≤ 4 * (Z * L) := by
    calc b * (1 + cc) ≤ (2 * Z) * (2 * L) := mul_le_mul hb hc hc0 (by linarith)
      _ = 4 * (Z * L) := by ring
  have hBb : (16 * (p * p) + 4 * q) * (2 + d) ≤ 40 * (Z * L) := by
    calc (16 * (p * p) + 4 * q) * (2 + d) ≤ (20 * Z) * (2 * L) := mul_le_mul hpq hd hd0 (by linarith)
      _ = 40 * (Z * L) := by ring
  have hin : b * (1 + cc) + (16 * (p * p) + 4 * q) * (2 + d) ≤ 44 * (Z * L) := by
    nlinarith [hA, hBb]
  calc cc * (b * (1 + cc) + (16 * (p * p) + 4 * q) * (2 + d))
      ≤ cc * (44 * (Z * L)) := by apply mul_le_mul_of_nonneg_left hin hf0
    _ ≤ (2 * L) * (44 * (Z * L)) := by apply mul_le_mul_of_nonneg_right hf (by positivity)
    _ = 88 * (Z * L ^ 2) := by ring
    _ ≤ 90 * (Z * L ^ 3) := by
        nlinarith [mul_nonneg (mul_nonneg hZ0 (sq_nonneg L)) (show (0:ℝ) ≤ 90 * L - 88 by linarith)]

lemma csup_g4 (a t1 t2 t3 t4 Z L : ℝ)
    (ha : a ≤ L) (ha0 : 0 ≤ a) (h1 : t1 ≤ 16 * Z) (h2 : t2 ≤ 12 * (Z * L))
    (h3 : t3 ≤ 64 * (Z * L)) (h4 : t4 ≤ 12 * (Z * L ^ 2)) (hZ0 : 0 ≤ Z) (hL1 : 1 ≤ L) :
    a * (t1 + t2 + t3 + t4) ≤ 110 * (Z * L ^ 3) := by
  have hin : t1 + t2 + t3 + t4 ≤ 110 * (Z * L ^ 2) := by
    nlinarith [h1, h2, h3, h4, mul_nonneg hZ0 (show (0:ℝ) ≤ L ^ 2 - 1 by nlinarith [hL1]),
      mul_nonneg (mul_nonneg hZ0 (show (0:ℝ) ≤ L by linarith)) (show (0:ℝ) ≤ L - 1 by linarith)]
  calc a * (t1 + t2 + t3 + t4) ≤ a * (110 * (Z * L ^ 2)) := mul_le_mul_of_nonneg_left hin ha0
    _ ≤ L * (110 * (Z * L ^ 2)) := mul_le_mul_of_nonneg_right ha (by positivity)
    _ = 110 * (Z * L ^ 3) := by ring

/-- **The minor-arc `Csup` asymptotic**: for `U=V=P` with `P³ ≤ N` and `P·Q ≤ N`,
    `minorCsup ≤ 200·N·(log N + 2)³/√P` — the `N/√P·polylog` bound that closes the minor
    L⁴ smallness once `P = (log N)^B`, `B ≥ 8`. -/
lemma minorCsup_bound (N P Q : ℕ) (hP2 : 2 ≤ P) (hPN : P ^ 3 ≤ N) (hPQ : P * Q ≤ N) :
    minorCsup N P P P Q ≤ 300 * (N : ℝ) * (Real.log N + 2) ^ 3 / Real.sqrt P := by
  have hP1 : 1 ≤ P := by omega
  have hPR : (2 : ℝ) ≤ (P : ℝ) := by exact_mod_cast hP2
  have hN8 : 8 ≤ N := le_trans (by norm_num : (8:ℕ) ≤ 2^3) (le_trans (Nat.pow_le_pow_left hP2 3) hPN)
  have hNR : (8 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN8
  have hPcube : (P : ℝ) ≤ (P : ℝ) ^ 3 := by
    have h1 : (1 : ℝ) ≤ (P : ℝ) ^ 2 := by nlinarith [hPR]
    calc (P : ℝ) = P * 1 := by ring
      _ ≤ P * P ^ 2 := by apply mul_le_mul_of_nonneg_left h1 (by linarith)
      _ = P ^ 3 := by ring
  have hPNR : (P : ℝ) ≤ (N : ℝ) := le_trans hPcube (by exact_mod_cast hPN)
  have hPQR : (P : ℝ) * Q ≤ N := by exact_mod_cast hPQ
  have hQ0R : (0:ℝ) ≤ (Q:ℝ) := by positivity
  have hQR : (Q : ℝ) ≤ N := by
    nlinarith [hPQR, hPR, hQ0R, mul_nonneg (show (0:ℝ) ≤ (P:ℝ) - 1 by linarith) hQ0R]
  have hsP1 : (1 : ℝ) ≤ Real.sqrt P := by
    rw [show (1:ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    exact Real.sqrt_le_sqrt (by linarith)
  have hsPpos : (0 : ℝ) < Real.sqrt P := by linarith
  have hlogN0 : (0 : ℝ) ≤ Real.log N := Real.log_nonneg (by linarith)
  have hlogNP : Real.log P ≤ Real.log N := Real.log_le_log (by linarith) hPNR
  have hlogQN : Real.log Q ≤ Real.log N := by
    rcases Nat.eq_zero_or_pos Q with hQ0 | hQ0
    · simp [hQ0]; positivity
    · exact Real.log_le_log (by exact_mod_cast hQ0) hQR
  have hlog2QN : Real.log (2 * (Q:ℝ)) ≤ Real.log N + 1 := by
    rcases Nat.eq_zero_or_pos Q with hQ0 | hQ0
    · simp [hQ0]; linarith
    · have : Real.log (2 * (Q:ℝ)) = Real.log 2 + Real.log Q := Real.log_mul (by norm_num) (by
        exact_mod_cast hQ0.ne')
      rw [this]
      nlinarith [hlogQN, Real.log_two_lt_d9]
  -- √-helpers (all from P³ ≤ N, PQ ≤ N)
  have hPcubeR : (P : ℝ) ^ 3 ≤ N := by exact_mod_cast hPN
  have hsqrtN : Real.sqrt N ≤ N := by
    have h : Real.sqrt (N : ℝ) ≤ Real.sqrt ((N : ℝ) ^ 2) := Real.sqrt_le_sqrt (by nlinarith [hNR])
    rwa [Real.sqrt_sq (by positivity)] at h
  have hPsP : (P : ℝ) * Real.sqrt P ≤ N := by
    have h : (P : ℝ) * Real.sqrt P = Real.sqrt ((P : ℝ) ^ 3) := by
      rw [show (P : ℝ) ^ 3 = (P : ℝ) ^ 2 * P by ring, Real.sqrt_mul (by positivity),
        Real.sqrt_sq (by positivity)]
    rw [h]
    exact le_trans (Real.sqrt_le_sqrt hPcubeR) hsqrtN
  have hP2sP : (P : ℝ) ^ 2 * Real.sqrt P ≤ N := by
    have h : (P : ℝ) ^ 2 * Real.sqrt P = Real.sqrt ((P : ℝ) ^ 5) := by
      rw [show (P : ℝ) ^ 5 = ((P : ℝ) ^ 2) ^ 2 * P by ring, Real.sqrt_mul (by positivity),
        Real.sqrt_sq (by positivity)]
    rw [h]
    have hP5 : (P : ℝ) ^ 5 ≤ (N : ℝ) ^ 2 := by
      have h6 : ((P : ℝ) ^ 3) ^ 2 ≤ (N : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hPcubeR 2
      nlinarith [h6, mul_nonneg (pow_nonneg (show (0:ℝ) ≤ (P:ℝ) by linarith) 5)
        (show (0:ℝ) ≤ (P:ℝ) - 1 by linarith)]
    calc Real.sqrt ((P : ℝ) ^ 5) ≤ Real.sqrt ((N : ℝ) ^ 2) := Real.sqrt_le_sqrt hP5
      _ = N := Real.sqrt_sq (by positivity)
  have hsqrtPsq : Real.sqrt P / P = 1 / Real.sqrt P := by
    rw [div_eq_div_iff (ne_of_gt (show (0:ℝ) < (P:ℝ) by linarith)) (ne_of_gt hsPpos), one_mul]
    exact Real.mul_self_sqrt (by linarith)
  have hQsP : (Q : ℝ) * Real.sqrt P ≤ N := by
    have hQle : (Q : ℝ) ≤ N / P := by rw [le_div_iff₀ (by linarith)]; nlinarith [hPQR]
    calc (Q : ℝ) * Real.sqrt P ≤ (N / P) * Real.sqrt P :=
          mul_le_mul_of_nonneg_right hQle (Real.sqrt_nonneg _)
      _ = N * (Real.sqrt P / P) := by ring
      _ = N * (1 / Real.sqrt P) := by rw [hsqrtPsq]
      _ ≤ N * 1 := by
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          rw [div_le_one hsPpos]; exact hsP1
      _ = N := by ring
  -- yardstick facts
  set L : ℝ := Real.log N + 2 with hLdef
  have hL2 : (2 : ℝ) ≤ L := by rw [hLdef]; linarith
  have hL1 : (1 : ℝ) ≤ L := by linarith
  have hL0 : (0 : ℝ) ≤ L := by linarith
  set Y : ℝ := (N : ℝ) * L ^ 3 / Real.sqrt P with hYdef
  have hYpos : (0 : ℝ) ≤ Y := by rw [hYdef]; positivity
  -- helper: X ≤ c·Y  from  X·√P ≤ c·N·L³
  have hbnd : ∀ (X c : ℝ), 0 ≤ c → X * Real.sqrt P ≤ c * (N * L ^ 3) → X ≤ c * Y := by
    intro X c hc hX
    rw [hYdef, show c * ((N : ℝ) * L ^ 3 / Real.sqrt P) = c * (N * L ^ 3) / Real.sqrt P by ring,
      le_div_iff₀ hsPpos]
    exact hX
  have hlog1P : (1 : ℝ) + Real.log P ≤ L := by rw [hLdef]; linarith [hlogNP]
  have hlogN1 : Real.log (↑N + 1) ≤ L := by
    rw [hLdef]
    have : Real.log (↑N + 1) ≤ Real.log (2 * N) := Real.log_le_log (by linarith) (by linarith)
    rw [Real.log_mul (by norm_num) (by positivity)] at this
    nlinarith [this, Real.log_two_lt_d9]
  have hlog2Q_L : (2 : ℝ) + Real.log (2 * (Q : ℝ)) ≤ 2 * L := by rw [hLdef]; linarith [hlog2QN]
  have hlogPP : (1 : ℝ) + Real.log (↑P * ↑P) ≤ 2 * L := by
    rw [Real.log_mul (by positivity) (by positivity)]; rw [hLdef]; linarith [hlogNP]
  have hlogPP2 : Real.log (↑P * ↑P) ≤ 2 * L := by
    rw [Real.log_mul (by positivity) (by positivity)]; rw [hLdef]; linarith [hlogNP]
  have hlogN_L : Real.log N ≤ L := by rw [hLdef]; linarith
  have hlogP_L : Real.log P ≤ L := by rw [hLdef]; linarith [hlogNP]
  have hk_L : ((Nat.log 2 N + 1 : ℕ) : ℝ) ≤ 2 * L := by
    push_cast
    have := natlog2_le_two_log N (by omega)
    rw [hLdef]; linarith
  -- Z := N/√P, Y = Z·L³
  set Z : ℝ := (N : ℝ) / Real.sqrt P with hZdef
  have hZ0 : (0 : ℝ) ≤ Z := by rw [hZdef]; positivity
  have hYZ : Y = Z * L ^ 3 := by rw [hYdef, hZdef]; ring
  have hsPP : Real.sqrt P ≤ P := by
    nlinarith [Real.mul_self_sqrt (show (0:ℝ) ≤ (P:ℝ) by linarith), hsP1]
  have hlog2Q_nonneg : (0 : ℝ) ≤ Real.log (2 * (Q : ℝ)) := by
    rcases Nat.eq_zero_or_pos Q with hQ0 | hQ0
    · simp [hQ0]
    · have hq1 : (1:ℝ) ≤ (Q:ℝ) := by exact_mod_cast hQ0
      exact Real.log_nonneg (by linarith)
  have h2NP : 2 * (N : ℝ) / P ≤ 2 * Z := by
    rw [hZdef, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_left (by positivity) hsPpos hsPP) (by norm_num)
  have hPZ : (P : ℝ) ≤ Z := by rw [hZdef, le_div_iff₀ hsPpos]; exact hPsP
  have hP2Z : (P : ℝ) ^ 2 ≤ Z := by rw [hZdef, le_div_iff₀ hsPpos]; exact hP2sP
  have hQZ : (Q : ℝ) ≤ Z := by rw [hZdef, le_div_iff₀ hsPpos]; exact hQsP
  have hlogP0 : (0 : ℝ) ≤ Real.log P := Real.log_nonneg (by linarith)
  have h2Q0 : (0 : ℝ) ≤ 2 + Real.log (2 * (Q : ℝ)) := by linarith [hlog2Q_nonneg]
  have hLL2 : L ≤ L ^ 2 := by nlinarith [hL1]
  have hZL : Z ≤ Z * L := by nlinarith [hZ0, hL1]
  have hZL2 : Z * L ^ 2 ≤ Y := by
    rw [hYZ]
    have : L ^ 2 ≤ L ^ 3 := by nlinarith [hL1, sq_nonneg L]
    nlinarith [hZ0, this]
  have hZL1 : Z * L ≤ Y := le_trans (by nlinarith [hZ0, hLL2]) hZL2
  -- √(NQL) ≤ Z·L
  have hsqNQL : Real.sqrt ((N : ℝ) * Q * (1 + Real.log (2 * (Q : ℝ)))) ≤ Z * L := by
    have harg : (N : ℝ) * Q * (1 + Real.log (2 * (Q : ℝ))) ≤ (Z * L) ^ 2 := by
      have hNQ : (N : ℝ) * Q ≤ Z ^ 2 := by
        rw [hZdef, div_pow, le_div_iff₀ (by positivity), Real.sq_sqrt (by linarith)]
        nlinarith [mul_le_mul_of_nonneg_left hPQR (show (0:ℝ) ≤ (N:ℝ) by positivity)]
      have h1L : (1 : ℝ) + Real.log (2 * (Q : ℝ)) ≤ L ^ 2 := by
        have h1 : (1 : ℝ) + Real.log (2 * (Q : ℝ)) ≤ L := by rw [hLdef]; linarith [hlog2QN]
        linarith [h1, hLL2]
      have hpos1 : (0:ℝ) ≤ 1 + Real.log (2 * (Q:ℝ)) := by linarith [hlog2Q_nonneg]
      calc (N : ℝ) * Q * (1 + Real.log (2 * (Q : ℝ)))
          ≤ Z ^ 2 * L ^ 2 := mul_le_mul hNQ h1L hpos1 (by positivity)
        _ = (Z * L) ^ 2 := by ring
    calc Real.sqrt ((N : ℝ) * Q * (1 + Real.log (2 * (Q : ℝ))))
        ≤ Real.sqrt ((Z * L) ^ 2) := Real.sqrt_le_sqrt harg
      _ = Z * L := Real.sqrt_sq (by positivity)
  -- √(P+1) ≥ √P
  have hsqP1 : (N : ℝ) / Real.sqrt (↑P + 1) ≤ Z := by
    rw [hZdef]
    exact div_le_div_of_nonneg_left (by positivity) hsPpos (Real.sqrt_le_sqrt (by linarith))
  -- √(1+log2Q) ≤ L
  have hsq1L : Real.sqrt (1 + Real.log (2 * (Q : ℝ))) ≤ L := by
    rw [show L = Real.sqrt (L ^ 2) from (Real.sqrt_sq (by linarith)).symm]
    apply Real.sqrt_le_sqrt
    have h1 : (1 : ℝ) + Real.log (2 * (Q : ℝ)) ≤ L := by rw [hLdef]; linarith [hlog2QN]
    linarith [h1, hLL2]
  -- assemble via abstract group lemmas (light instantiations)
  have hlogN10 : (0 : ℝ) ≤ Real.log (↑N + 1) := by
    have hn1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
    exact Real.log_nonneg (by linarith)
  have hlogPP0 : (0 : ℝ) ≤ Real.log (↑P * ↑P) := Real.log_nonneg (by nlinarith [hPR])
  have hZL3 : (0 : ℝ) ≤ Z * L ^ 3 := by rw [← hYZ]; exact hYpos
  have hk0 : (0 : ℝ) ≤ ((Nat.log 2 N + 1 : ℕ) : ℝ) := by positivity
  have hs10 : Real.sqrt 10 ≤ 4 := by
    rw [show (4 : ℝ) = Real.sqrt 16 by rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hs32 : Real.sqrt 32 ≤ 6 := by
    rw [show (6 : ℝ) = Real.sqrt 36 by rw [show (36 : ℝ) = 6 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hB1 := csup_g1 (Real.log (↑N + 1)) (2 * ↑N / ↑P) (Real.log ↑P) (Real.log (2 * ↑Q)) ↑P ↑Q Z L
    hlogN1 hlogN10 h2NP hlog1P (by linarith [hlogP0]) (by linarith [hPZ, hQZ]) hlog2Q_L h2Q0
    (le_trans hPZ hZL) hZ0 hL1
  have hB2 := csup_g2 (2 * ↑N / ↑P) (Real.log (↑P * ↑P)) (Real.log (2 * ↑Q)) ↑P ↑Q Z L
    hlogPP2 hlogPP0 h2NP hlogPP (by linarith [hlogPP0]) (by nlinarith [hP2Z, hQZ]) hlog2Q_L h2Q0
    hZ0 hL1
  have hB3 : (↑P : ℝ) * Real.log ↑P ≤ 4 * (Z * L ^ 3) := by
    have h1 : (↑P : ℝ) * Real.log ↑P ≤ Z * L := mul_le_mul hPZ hlogP_L hlogP0 hZ0
    nlinarith [h1, hZ0, hL1,
      mul_nonneg (mul_nonneg hZ0 (show (0:ℝ) ≤ L by linarith)) (show (0:ℝ) ≤ 4 * L ^ 2 - 1 by nlinarith [hL1])]
  have hT1 : 4 * Real.sqrt 10 * ↑N / Real.sqrt (↑P + 1) ≤ 16 * Z := by
    rw [show 4 * Real.sqrt 10 * ↑N / Real.sqrt (↑P + 1)
        = (4 * Real.sqrt 10) * ((N : ℝ) / Real.sqrt (↑P + 1)) by ring]
    calc (4 * Real.sqrt 10) * ((N : ℝ) / Real.sqrt (↑P + 1))
        ≤ (4 * Real.sqrt 10) * Z := mul_le_mul_of_nonneg_left hsqP1 (by positivity)
      _ ≤ 16 * Z := by nlinarith [hs10, hZ0]
  have hT2 : Real.sqrt 32 * ↑N * ((Nat.log 2 N + 1 : ℕ) : ℝ) / Real.sqrt ↑P ≤ 12 * (Z * L) := by
    rw [show Real.sqrt 32 * ↑N * ((Nat.log 2 N + 1 : ℕ) : ℝ) / Real.sqrt ↑P
        = (Real.sqrt 32 * ((Nat.log 2 N + 1 : ℕ) : ℝ)) * Z by rw [hZdef]; ring]
    calc (Real.sqrt 32 * ((Nat.log 2 N + 1 : ℕ) : ℝ)) * Z ≤ (6 * (2 * L)) * Z := by
          apply mul_le_mul_of_nonneg_right _ hZ0
          calc Real.sqrt 32 * ((Nat.log 2 N + 1 : ℕ) : ℝ) ≤ 6 * ((Nat.log 2 N + 1 : ℕ) : ℝ) := by
                nlinarith [hs32, hk0]
            _ ≤ 6 * (2 * L) := by nlinarith [hk_L]
      _ = 12 * (Z * L) := by ring
  have hT3 : 64 * ↑N * Real.sqrt (1 + Real.log (2 * ↑Q)) / Real.sqrt ↑P ≤ 64 * (Z * L) := by
    rw [show 64 * ↑N * Real.sqrt (1 + Real.log (2 * ↑Q)) / Real.sqrt ↑P
        = (64 * Real.sqrt (1 + Real.log (2 * ↑Q))) * Z by rw [hZdef]; ring]
    calc (64 * Real.sqrt (1 + Real.log (2 * ↑Q))) * Z ≤ (64 * L) * Z := by
          apply mul_le_mul_of_nonneg_right _ hZ0; nlinarith [hsq1L]
      _ = 64 * (Z * L) := by ring
  have hT4 : 6 * ((Nat.log 2 N + 1 : ℕ) : ℝ) * Real.sqrt (↑N * ↑Q * (1 + Real.log (2 * ↑Q)))
      ≤ 12 * (Z * L ^ 2) := by
    calc 6 * ((Nat.log 2 N + 1 : ℕ) : ℝ) * Real.sqrt (↑N * ↑Q * (1 + Real.log (2 * ↑Q)))
        ≤ 6 * (2 * L) * (Z * L) :=
          mul_le_mul (by nlinarith [hk_L]) hsqNQL (Real.sqrt_nonneg _) (by positivity)
      _ = 12 * (Z * L ^ 2) := by ring
  have hB4 := csup_g4 (Real.log ↑N) (4 * Real.sqrt 10 * ↑N / Real.sqrt (↑P + 1))
    (Real.sqrt 32 * ↑N * ((Nat.log 2 N + 1 : ℕ) : ℝ) / Real.sqrt ↑P)
    (64 * ↑N * Real.sqrt (1 + Real.log (2 * ↑Q)) / Real.sqrt ↑P)
    (6 * ((Nat.log 2 N + 1 : ℕ) : ℝ) * Real.sqrt (↑N * ↑Q * (1 + Real.log (2 * ↑Q)))) Z L
    hlogN_L hlogN0 hT1 hT2 hT3 hT4 hZ0 hL1
  unfold minorCsup
  rw [show (300 : ℝ) * ↑N * L ^ 3 / Real.sqrt ↑P = 300 * (Z * L ^ 3) by rw [hZdef]; ring]
  refine (add_le_add (add_le_add (add_le_add hB1 hB2) hB3) hB4).trans ?_
  linarith [hZL3]

end MinorArc

set_option maxHeartbeats 1000000

/-!
# Minor-arc exponential-sum bound

The geometric foundation of the circle method's **minor arcs** (the input, alongside
Vaughan's identity, to the Vinogradov bound on `∑ Λ(n) e(nα)` that drives almost-all
binary Goldbach — see `AlmostAllGoldbachReduction.lean`).

Main results:
  • `MinorArc.exp_sum_bound` — `‖∑_{n<N} e(nα)‖ ≤ 1 / (2 · dist(α, ℤ))`  for `α ∉ ℤ`,
    where `e(x) = exp(2πi x)` and `dist(α, ℤ) = |α - round α|`.
  • `MinorArc.char_orthogonality` — `∑_{n<q} e(an/q) = q·[q∣a]`, additive-character
    orthogonality (backbone of Gauss/Ramanujan sums + the major-arc singular series).
  • `MinorArc.integral_e` — `∫₀¹ e(kα) dα = [k=0]`, integral character orthogonality
    (circle-method main-term extractor; seed of the Parseval → large-sieve chain).
  • `MinorArc.parseval` — `∫₀¹ ‖∑_{n<N} aₙ e(nα)‖² dα = ∑_{n<N} ‖aₙ‖²`, the L² mean
    value of an exponential sum (the circle-method variance engine; large-sieve base case).

Proof route (all elementary, Mathlib-only):
  • `geom_exp_bound`   — for unit `z ≠ 1`, `‖∑_{n<N} zⁿ‖ ≤ 2/‖z-1‖`  (geometric sum + triangle).
  • `e_sub_one_norm`   — `‖e(α)-1‖ = 2|sin(πα)|`  (chord length, via `normSq` + double angle).
  • `exp_sum_le_sin`   — combine the two: `‖∑ e(nα)‖ ≤ 1/|sin(πα)|`.
  • `two_dist_le_abs_sin` — Jordan's inequality `2·dist(α,ℤ) ≤ |sin(πα)|`
                            (`Real.le_sin_mul` + `sin_add_int_mul_pi` periodicity).
  • `exp_sum_bound`    — chain them to the `dist` form.

`#print axioms MinorArc.exp_sum_bound` = `[propext, Classical.choice, Quot.sound]` — axiom-free.
Pinned: `leanprover/lean4:v4.31.0` + Mathlib v4.31.0.
-/

namespace MinorArc

open Finset







/-- `e` on an integer is `1`. -/
lemma e_int (a : ℤ) : e ((a : ℝ)) = 1 := (e_eq_one_iff _).mpr ⟨a, rfl⟩

/-- **Additive-character orthogonality**: `∑_{n<q} e(an/q) = q` if `q ∣ a`, else `0`.
    The backbone of Gauss/Ramanujan sums and the major-arc singular series. -/
lemma char_orthogonality (a : ℤ) (q : ℕ) (hq : q ≠ 0) :
    ∑ n ∈ Finset.range q, e ((a : ℝ) * n / q) = if (q : ℤ) ∣ a then (q : ℂ) else 0 := by
  have hqR : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq
  have hterm : ∀ n : ℕ, e ((a : ℝ) * n / q) = (e ((a : ℝ) / q)) ^ n := by
    intro n
    rw [← e_pow, show (n : ℝ) * ((a : ℝ) / q) = (a : ℝ) * n / q by ring]
  rw [Finset.sum_congr rfl (fun n _ => hterm n)]
  have hzq : (e ((a : ℝ) / q)) ^ q = 1 := by
    rw [← e_pow, show (q : ℝ) * ((a : ℝ) / q) = (a : ℝ) by field_simp]
    exact e_int a
  by_cases hdvd : (q : ℤ) ∣ a
  · obtain ⟨k, hk⟩ := hdvd
    have hz : e ((a : ℝ) / q) = 1 := by
      rw [show ((a : ℝ) / q) = (k : ℝ) by rw [hk]; push_cast; field_simp]
      exact e_int k
    rw [if_pos ⟨k, hk⟩]
    simp [hz]
  · have hzne : e ((a : ℝ) / q) ≠ 1 := by
      intro hz
      rw [e_eq_one_iff] at hz
      obtain ⟨k, hk⟩ := hz
      apply hdvd
      refine ⟨k, ?_⟩
      have h1 : (a : ℝ) = (k : ℝ) * (q : ℝ) := by rw [← hk]; field_simp
      have h2 : (a : ℝ) = (q : ℝ) * (k : ℝ) := by rw [h1]; ring
      exact_mod_cast h2
    rw [geom_sum_eq hzne, hzq, sub_self, zero_div, if_neg hdvd]

/-- **Integral character orthogonality**: `∫₀¹ e(kα) dα = 1` if `k = 0`, else `0`.
    The circle-method main-term extractor and the seed of the Parseval/large-sieve chain. -/
lemma integral_e (k : ℤ) :
    ∫ α in (0:ℝ)..1, e ((k : ℝ) * α) = if k = 0 then 1 else 0 := by
  by_cases hk : k = 0
  · subst hk
    rw [if_pos rfl]
    have hcong : ∀ α ∈ Set.uIcc (0:ℝ) 1, e (((0 : ℤ) : ℝ) * α) = 1 := by
      intro α _; simp only [Int.cast_zero, zero_mul]; simp [e]
    rw [intervalIntegral.integral_congr hcong, intervalIntegral.integral_const]
    norm_num
  · rw [if_neg hk]
    set c : ℂ := 2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) with hc
    have hcne : c ≠ 0 := by
      rw [hc]
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
        (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero)
        (by exact_mod_cast hk)
    have hexpc : Complex.exp c = 1 := by
      rw [hc, Complex.exp_eq_one_iff]; exact ⟨k, by ring⟩
    have hderiv : ∀ α ∈ Set.uIcc (0:ℝ) 1,
        HasDerivAt (fun α : ℝ => Complex.exp (c * ↑α) / c) (e ((k : ℝ) * α)) α := by
      intro α _
      have h1 : HasDerivAt (fun α : ℝ => c * (↑α : ℂ)) c α := by
        simpa using (Complex.ofRealCLM.hasDerivAt).const_mul c
      have h2 : HasDerivAt (fun α : ℝ => Complex.exp (c * ↑α))
          (Complex.exp (c * ↑α) * c) α := h1.cexp
      have h3 := h2.div_const c
      rw [mul_div_assoc, div_self hcne, mul_one] at h3
      have hval : e ((k : ℝ) * α) = Complex.exp (c * ↑α) := by
        rw [e, hc]; push_cast; ring_nf
      rw [hval]; exact h3
    have hcont : IntervalIntegrable (fun α : ℝ => e ((k : ℝ) * α)) MeasureTheory.volume 0 1 := by
      apply Continuous.intervalIntegrable; unfold e; fun_prop
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont]
    rw [Complex.ofReal_one, Complex.ofReal_zero, mul_one, mul_zero, Complex.exp_zero, hexpc]
    ring

/-- Orthogonality with natural indices: `∫₀¹ e((m−n)α) dα = [m = n]`. -/
lemma integral_e_nat (m n : ℕ) :
    ∫ α in (0:ℝ)..1, e (((m : ℝ) - n) * α) = if m = n then 1 else 0 := by
  have h := integral_e ((m : ℤ) - n)
  have hcast : (((m : ℤ) - (n : ℤ) : ℤ) : ℝ) = (m : ℝ) - n := by push_cast; ring
  rw [hcast] at h
  simpa only [sub_eq_zero, Int.natCast_inj] using h

/-- **Fourier extraction of the representation count**: the `n`-th Fourier coefficient of
    `S(α)²` is the twofold representation sum `R(n) = ∑_{m+k=n} aₘaₖ` — the bridge from
    the circle integral to Goldbach counts. -/
lemma fourier_coeff_sq (a : ℕ → ℂ) (N n : ℕ) :
    ∫ α in (0:ℝ)..1,
        (∑ m ∈ Finset.range N, a m * e ((m : ℝ) * α)) ^ 2 * e (-((n : ℝ) * α))
      = ∑ p ∈ (Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 = n),
          a p.1 * a p.2 := by
  have hint : ∀ m k : ℕ, IntervalIntegrable
      (fun α : ℝ => (a m * a k) * e ((((m : ℤ) + k - n : ℤ) : ℝ) * α))
      MeasureTheory.volume 0 1 := by
    intro m k
    apply Continuous.intervalIntegrable; unfold e; fun_prop
  have hint2 : ∀ m : ℕ, IntervalIntegrable
      (fun α : ℝ => ∑ k ∈ Finset.range N,
        (a m * a k) * e ((((m : ℤ) + k - n : ℤ) : ℝ) * α))
      MeasureTheory.volume 0 1 := by
    intro m
    apply Continuous.intervalIntegrable
    apply continuous_finsetSum
    intro k _
    unfold e; fun_prop
  have hpt : ∀ α ∈ Set.uIcc (0:ℝ) 1,
      (∑ m ∈ Finset.range N, a m * e ((m : ℝ) * α)) ^ 2 * e (-((n : ℝ) * α))
      = ∑ m ∈ Finset.range N, ∑ k ∈ Finset.range N,
          (a m * a k) * e ((((m : ℤ) + k - n : ℤ) : ℝ) * α) := by
    intro α _
    rw [sq, Finset.sum_mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro m _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl; intro k _
    have harg : (((m : ℤ) + k - n : ℤ) : ℝ) * α
        = (m : ℝ) * α + ((k : ℝ) * α + (-((n : ℝ) * α))) := by
      push_cast; ring
    rw [harg, ← e_add, ← e_add]
    ring
  rw [intervalIntegral.integral_congr hpt,
    intervalIntegral.integral_finsetSum (fun m _ => hint2 m)]
  have hinner : ∀ m ∈ Finset.range N,
      (∫ α in (0:ℝ)..1, ∑ k ∈ Finset.range N,
        (a m * a k) * e ((((m : ℤ) + k - n : ℤ) : ℝ) * α))
      = ∑ k ∈ Finset.range N, if m + k = n then a m * a k else 0 := by
    intro m _
    rw [intervalIntegral.integral_finsetSum (fun k _ => hint m k)]
    apply Finset.sum_congr rfl; intro k _
    rw [intervalIntegral.integral_const_mul, integral_e ((m : ℤ) + k - n)]
    have hiff : ((m : ℤ) + k - n = 0) ↔ (m + k = n) := by omega
    by_cases h : m + k = n
    · rw [if_pos (hiff.mpr h), if_pos h, mul_one]
    · rw [if_neg (fun hc => h (hiff.mp hc)), if_neg h, mul_zero]
  rw [Finset.sum_congr rfl hinner, Finset.sum_filter, Finset.sum_product]

/-- Parseval, complex pairing form: `∫₀¹ S·conj S = ∑ aₙ·conj aₙ`. -/
lemma parseval_aux (a : ℕ → ℂ) (N : ℕ) :
    ∫ α in (0:ℝ)..1,
        (∑ m ∈ Finset.range N, a m * e (m * α)) *
          (starRingEnd ℂ) (∑ n ∈ Finset.range N, a n * e (n * α))
      = ∑ n ∈ Finset.range N, a n * (starRingEnd ℂ) (a n) := by
  have hint : ∀ m n : ℕ, IntervalIntegrable
      (fun α : ℝ => (a m * (starRingEnd ℂ) (a n)) * e (((m : ℝ) - n) * α))
      MeasureTheory.volume 0 1 := by
    intro m n
    apply Continuous.intervalIntegrable; unfold e; fun_prop
  have hint2 : ∀ m : ℕ, IntervalIntegrable
      (fun α : ℝ => ∑ n ∈ Finset.range N,
        (a m * (starRingEnd ℂ) (a n)) * e (((m : ℝ) - n) * α))
      MeasureTheory.volume 0 1 := by
    intro m
    apply Continuous.intervalIntegrable
    apply continuous_finsetSum
    intro n _
    unfold e; fun_prop
  have hpt : ∀ α ∈ Set.uIcc (0:ℝ) 1,
      (∑ m ∈ Finset.range N, a m * e (m * α)) *
        (starRingEnd ℂ) (∑ n ∈ Finset.range N, a n * e (n * α))
      = ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
          (a m * (starRingEnd ℂ) (a n)) * e (((m : ℝ) - n) * α) := by
    intro α _
    rw [map_sum, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro m _
    apply Finset.sum_congr rfl; intro n _
    rw [map_mul, e_conj]
    have h1 : e ((m : ℝ) * α) * e (-((n : ℝ) * α)) = e (((m : ℝ) - n) * α) := by
      rw [e_add]; congr 1; ring
    calc a m * e ((m : ℝ) * α) * ((starRingEnd ℂ) (a n) * e (-((n : ℝ) * α)))
        = a m * (starRingEnd ℂ) (a n) * (e ((m : ℝ) * α) * e (-((n : ℝ) * α))) := by ring
      _ = a m * (starRingEnd ℂ) (a n) * e (((m : ℝ) - n) * α) := by rw [h1]
  rw [intervalIntegral.integral_congr hpt]
  rw [intervalIntegral.integral_finsetSum (fun m _ => hint2 m)]
  have hinner : ∀ m ∈ Finset.range N,
      (∫ α in (0:ℝ)..1, ∑ n ∈ Finset.range N,
        (a m * (starRingEnd ℂ) (a n)) * e (((m : ℝ) - n) * α))
      = a m * (starRingEnd ℂ) (a m) := by
    intro m hm
    rw [intervalIntegral.integral_finsetSum (fun n _ => hint m n)]
    have hterm : ∀ n ∈ Finset.range N,
        (∫ α in (0:ℝ)..1, (a m * (starRingEnd ℂ) (a n)) * e (((m : ℝ) - n) * α))
        = (a m * (starRingEnd ℂ) (a n)) * (if m = n then 1 else 0) := by
      intro n _
      rw [intervalIntegral.integral_const_mul, integral_e_nat]
    rw [Finset.sum_congr rfl hterm]
    rw [Finset.sum_eq_single m
      (fun n _ hne => by rw [if_neg (fun h => hne h.symm), mul_zero])
      (fun hm' => absurd hm hm')]
    rw [if_pos rfl, mul_one]
  exact Finset.sum_congr rfl hinner

/-- **Parseval / the L² mean value of an exponential sum**:
    `∫₀¹ ‖∑_{n<N} aₙ e(nα)‖² dα = ∑_{n<N} ‖aₙ‖²`. The engine of the circle-method
    variance computation and the base case of the large sieve. -/
lemma parseval (a : ℕ → ℂ) (N : ℕ) :
    ∫ α in (0:ℝ)..1, ‖∑ n ∈ Finset.range N, a n * e (n * α)‖ ^ 2
      = ∑ n ∈ Finset.range N, ‖a n‖ ^ 2 := by
  have key := parseval_aux a N
  have hpt : ∀ z : ℂ, z * (starRingEnd ℂ) z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    intro z
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hL : (∫ α in (0:ℝ)..1,
      (∑ m ∈ Finset.range N, a m * e (m * α)) *
        (starRingEnd ℂ) (∑ n ∈ Finset.range N, a n * e (n * α)))
      = ((∫ α in (0:ℝ)..1, ‖∑ n ∈ Finset.range N, a n * e (n * α)‖ ^ 2 : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro α _
    exact hpt _
  have hR : (∑ n ∈ Finset.range N, a n * (starRingEnd ℂ) (a n))
      = ((∑ n ∈ Finset.range N, ‖a n‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    exact Finset.sum_congr rfl (fun n _ => hpt (a n))
  rw [hL, hR] at key
  exact_mod_cast key







/-- `S(α)²` is itself a trig polynomial, with coefficients the representation sums
    `R(n) = ∑_{m+k=n} aₘaₖ`. -/
lemma sq_expsum_eq (a : ℕ → ℂ) (N : ℕ) (α : ℝ) :
    (∑ m ∈ Finset.range N, a m * e ((m : ℝ) * α)) ^ 2
      = ∑ n ∈ Finset.range (2 * N),
          (∑ p ∈ (Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 = n),
            a p.1 * a p.2) * e ((n : ℝ) * α) := by
  rw [sq, Finset.sum_mul_sum, ← Finset.sum_product']
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun p : ℕ × ℕ => p.1 + p.2)
      (t := Finset.range (2 * N))
      (fun p hp => by
        rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
        rw [Finset.mem_range]
        omega)]
  apply Finset.sum_congr rfl
  intro n _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.mem_filter] at hp
  have harg : (p.1 : ℝ) * α + (p.2 : ℝ) * α = (n : ℝ) * α := by
    rw [← hp.2]; push_cast; ring
  calc a p.1 * e ((p.1 : ℝ) * α) * (a p.2 * e ((p.2 : ℝ) * α))
      = a p.1 * a p.2 * (e ((p.1 : ℝ) * α) * e ((p.2 : ℝ) * α)) := by ring
    _ = a p.1 * a p.2 * e ((n : ℝ) * α) := by rw [e_add, harg]

/-- **The variance identity**: `∑_{n<2N} ‖R(n)‖² = ∫₀¹ ‖S(α)‖⁴ dα` — Parseval applied to
    the trig polynomial `S²`. The bridge between the minor-arc L⁴ bound and the
    sum-over-n variance that `almost_all_goldbach_of_variance` consumes. -/
lemma sum_repCoeff_sq_eq_L4 (a : ℕ → ℂ) (N : ℕ) :
    ∑ n ∈ Finset.range (2 * N),
        ‖∑ p ∈ (Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 = n),
          a p.1 * a p.2‖ ^ 2
      = ∫ α in (0:ℝ)..1, ‖∑ m ∈ Finset.range N, a m * e ((m : ℝ) * α)‖ ^ 4 := by
  calc ∑ n ∈ Finset.range (2 * N),
        ‖∑ p ∈ (Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 = n),
          a p.1 * a p.2‖ ^ 2
      = ∫ α in (0:ℝ)..1, ‖∑ n ∈ Finset.range (2 * N),
          (∑ p ∈ (Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 = n),
            a p.1 * a p.2) * e ((n : ℝ) * α)‖ ^ 2 :=
        (parseval (fun n => ∑ p ∈ (Finset.range N ×ˢ Finset.range N).filter
          (fun p => p.1 + p.2 = n), a p.1 * a p.2) (2 * N)).symm
    _ = ∫ α in (0:ℝ)..1, ‖(∑ m ∈ Finset.range N, a m * e ((m : ℝ) * α)) ^ 2‖ ^ 2 := by
        apply intervalIntegral.integral_congr
        intro α _
        dsimp only
        rw [sq_expsum_eq]
    _ = ∫ α in (0:ℝ)..1, ‖∑ m ∈ Finset.range N, a m * e ((m : ℝ) * α)‖ ^ 4 := by
        apply intervalIntegral.integral_congr
        intro α _
        dsimp only
        rw [norm_pow, ← pow_mul]

/-- **Variance = L² error**: for ANY candidate main term `c(n)`, the variance
    `∑_{n<2N} ‖R(n) − c(n)‖²` equals `∫₀¹ ‖S(α)² − C(α)‖² dα` where `C` is the trig
    polynomial with coefficients `c`. Reduces the Goldbach variance hypothesis to an
    L² bound on the circle, which the arc dichotomy then splits. -/
lemma variance_eq_L2_error (a c : ℕ → ℂ) (N : ℕ) :
    ∑ n ∈ Finset.range (2 * N),
        ‖(∑ p ∈ (Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 = n),
            a p.1 * a p.2) - c n‖ ^ 2
      = ∫ α in (0:ℝ)..1,
          ‖(∑ m ∈ Finset.range N, a m * e ((m : ℝ) * α)) ^ 2
            - ∑ n ∈ Finset.range (2 * N), c n * e ((n : ℝ) * α)‖ ^ 2 := by
  calc ∑ n ∈ Finset.range (2 * N),
        ‖(∑ p ∈ (Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 = n),
            a p.1 * a p.2) - c n‖ ^ 2
      = ∫ α in (0:ℝ)..1, ‖∑ n ∈ Finset.range (2 * N),
          ((∑ p ∈ (Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 = n),
            a p.1 * a p.2) - c n) * e ((n : ℝ) * α)‖ ^ 2 :=
        (parseval (fun n => (∑ p ∈ (Finset.range N ×ˢ Finset.range N).filter
          (fun p => p.1 + p.2 = n), a p.1 * a p.2) - c n) (2 * N)).symm
    _ = ∫ α in (0:ℝ)..1,
          ‖(∑ m ∈ Finset.range N, a m * e ((m : ℝ) * α)) ^ 2
            - ∑ n ∈ Finset.range (2 * N), c n * e ((n : ℝ) * α)‖ ^ 2 := by
        apply intervalIntegral.integral_congr
        intro α _
        dsimp only
        rw [sq_expsum_eq]
        simp only [sub_mul, Finset.sum_sub_distrib]

open MeasureTheory in
/-- **Circle split**: the L² integral over `(0,1]` splits exactly into the minor-arc set
    and its complement (the major arcs). -/
lemma L2_circle_split (f : ℝ → ℂ) (hf : Continuous f) (m : Set ℝ)
    (hm : MeasurableSet m) (hsub : m ⊆ Set.Ioc (0:ℝ) 1) :
    ∫ α in (0:ℝ)..1, ‖f α‖ ^ 2
      = (∫ α in m, ‖f α‖ ^ 2) + ∫ α in Set.Ioc (0:ℝ) 1 \ m, ‖f α‖ ^ 2 := by
  have hi : IntegrableOn (fun α => ‖f α‖ ^ 2) (Set.Ioc (0:ℝ) 1) volume :=
    (hf.norm.pow 2).integrableOn_Ioc
  rw [intervalIntegral.integral_of_le zero_le_one,
    ← setIntegral_union Set.disjoint_sdiff_right (measurableSet_Ioc.diff hm)
      (hi.mono_set hsub) (hi.mono_set Set.diff_subset),
    Set.union_diff_cancel hsub]

open MeasureTheory in
/-- **Elementary L² triangle bound on a set**: `∫_m ‖f−g‖² ≤ 2∫_m‖f‖² + 2∫_m‖g‖²`. -/
lemma L2_diff_le (f g : ℝ → ℂ) (hf : Continuous f) (hg : Continuous g) (m : Set ℝ)
    (hm : MeasurableSet m) (hsub : m ⊆ Set.Ioc (0:ℝ) 1) :
    ∫ α in m, ‖f α - g α‖ ^ 2
      ≤ 2 * (∫ α in m, ‖f α‖ ^ 2) + 2 * ∫ α in m, ‖g α‖ ^ 2 := by
  have hif : IntegrableOn (fun α => ‖f α‖ ^ 2) m volume :=
    ((hf.norm.pow 2).integrableOn_Ioc).mono_set hsub
  have hig : IntegrableOn (fun α => ‖g α‖ ^ 2) m volume :=
    ((hg.norm.pow 2).integrableOn_Ioc).mono_set hsub
  have hifg : IntegrableOn (fun α => ‖f α - g α‖ ^ 2) m volume :=
    (((hf.sub hg).norm.pow 2).integrableOn_Ioc).mono_set hsub
  have hpt : ∀ α ∈ m, ‖f α - g α‖ ^ 2 ≤ 2 * ‖f α‖ ^ 2 + 2 * ‖g α‖ ^ 2 := by
    intro α _
    have h1 : ‖f α - g α‖ ≤ ‖f α‖ + ‖g α‖ := norm_sub_le _ _
    have h2 : ‖f α - g α‖ ^ 2 ≤ (‖f α‖ + ‖g α‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    nlinarith [sq_nonneg (‖f α‖ - ‖g α‖)]
  have hsum : IntegrableOn (fun α => 2 * ‖f α‖ ^ 2 + 2 * ‖g α‖ ^ 2) m volume := by
    exact (hif.const_mul 2).add (hig.const_mul 2)
  calc ∫ α in m, ‖f α - g α‖ ^ 2
      ≤ ∫ α in m, (2 * ‖f α‖ ^ 2 + 2 * ‖g α‖ ^ 2) :=
        setIntegral_mono_on hifg hsum hm hpt
    _ = 2 * (∫ α in m, ‖f α‖ ^ 2) + 2 * ∫ α in m, ‖g α‖ ^ 2 := by
        rw [integral_add (hif.const_mul 2) (hig.const_mul 2),
          integral_const_mul, integral_const_mul]

open MeasureTheory in
/-- L² mass on any sub-arc set is at most the full-circle L² mass. -/
lemma setL2_le_circle (f : ℝ → ℂ) (hf : Continuous f) (m : Set ℝ)
    (hsub : m ⊆ Set.Ioc (0:ℝ) 1) :
    ∫ α in m, ‖f α‖ ^ 2 ≤ ∫ α in (0:ℝ)..1, ‖f α‖ ^ 2 := by
  rw [intervalIntegral.integral_of_le zero_le_one]
  apply setIntegral_mono_set ((hf.norm.pow 2).integrableOn_Ioc)
  · filter_upwards with α using by positivity
  · exact HasSubset.Subset.eventuallyLE hsub

lemma expsum_continuous (a : ℕ → ℂ) (N : ℕ) :
    Continuous (fun α : ℝ => ∑ n ∈ Finset.range N, a n * e ((n : ℝ) * α)) := by
  apply continuous_finsetSum
  intro n _
  unfold e
  fun_prop

open MeasureTheory in
/-- General L⁴-on-a-set bound: sup on one factor, Parseval on the other. -/
lemma L4_set_bound (a : ℕ → ℂ) (N : ℕ) (m : Set ℝ) (hm : MeasurableSet m)
    (hsub : m ⊆ Set.Ioc (0:ℝ) 1) (Csup : ℝ)
    (hsup : ∀ α ∈ m, ‖∑ n ∈ Finset.range N, a n * e ((n : ℝ) * α)‖ ≤ Csup) :
    ∫ α in m, ‖(∑ n ∈ Finset.range N, a n * e ((n : ℝ) * α)) ^ 2‖ ^ 2
      ≤ Csup ^ 2 * ∑ n ∈ Finset.range N, ‖a n‖ ^ 2 := by
  set S := fun α : ℝ => ∑ n ∈ Finset.range N, a n * e ((n : ℝ) * α) with hS
  have hcont : Continuous S := expsum_continuous a N
  rcases Set.eq_empty_or_nonempty m with hempty | ⟨α₀, hα₀⟩
  · rw [hempty]
    simp only [Measure.restrict_empty, integral_zero_measure]
    exact mul_nonneg (sq_nonneg Csup) (Finset.sum_nonneg fun n _ => sq_nonneg _)
  have hCnn : 0 ≤ Csup := le_trans (norm_nonneg _) (hsup α₀ hα₀)
  have hint2 : IntegrableOn (fun α => ‖S α‖ ^ 2) m volume :=
    ((hcont.norm.pow 2).integrableOn_Ioc).mono_set hsub
  have hint4 : IntegrableOn (fun α => ‖S α ^ 2‖ ^ 2) m volume := by
    exact (((hcont.pow 2).norm.pow 2).integrableOn_Ioc).mono_set hsub
  calc ∫ α in m, ‖S α ^ 2‖ ^ 2
      ≤ ∫ α in m, Csup ^ 2 * ‖S α‖ ^ 2 := by
        apply setIntegral_mono_on hint4 (hint2.const_mul _) hm
        intro α hα
        rw [norm_pow]
        have hsq : ‖S α‖ ^ 2 ≤ Csup ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hsup α hα) 2
        calc (‖S α‖ ^ 2) ^ 2 = ‖S α‖ ^ 2 * ‖S α‖ ^ 2 := by ring
          _ ≤ Csup ^ 2 * ‖S α‖ ^ 2 := mul_le_mul_of_nonneg_right hsq (by positivity)
    _ = Csup ^ 2 * ∫ α in m, ‖S α‖ ^ 2 := by rw [integral_const_mul]
    _ ≤ Csup ^ 2 * ∑ n ∈ Finset.range N, ‖a n‖ ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        calc ∫ α in m, ‖S α‖ ^ 2 ≤ ∫ α in (0:ℝ)..1, ‖S α‖ ^ 2 :=
              setL2_le_circle S hcont m hsub
          _ = ∑ n ∈ Finset.range N, ‖a n‖ ^ 2 := parseval a N

open MeasureTheory in
/-- **THE VARIANCE ASSEMBLY**: for any coefficients `a`, main term `c`, and minor set `m`
    with sup bound `Csup`, the full variance is at most the (finished) minor contribution
    plus the major-arc L² integral — the SINGLE remaining analytic input. -/
theorem variance_le_of_arcs (a c : ℕ → ℂ) (N : ℕ) (m : Set ℝ) (hm : MeasurableSet m)
    (hsub : m ⊆ Set.Ioc (0:ℝ) 1) (Csup : ℝ)
    (hsup : ∀ α ∈ m, ‖∑ n ∈ Finset.range N, a n * e ((n : ℝ) * α)‖ ≤ Csup) :
    ∑ n ∈ Finset.range (2 * N),
        ‖(∑ p ∈ (Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 = n),
            a p.1 * a p.2) - c n‖ ^ 2
      ≤ 2 * (Csup ^ 2 * ∑ n ∈ Finset.range N, ‖a n‖ ^ 2)
        + 2 * ∑ n ∈ Finset.range (2 * N), ‖c n‖ ^ 2
        + ∫ α in Set.Ioc (0:ℝ) 1 \ m,
            ‖(∑ k ∈ Finset.range N, a k * e ((k : ℝ) * α)) ^ 2
              - ∑ n ∈ Finset.range (2 * N), c n * e ((n : ℝ) * α)‖ ^ 2 := by
  have hScont : Continuous (fun α : ℝ => ∑ n ∈ Finset.range N, a n * e ((n : ℝ) * α)) :=
    expsum_continuous a N
  have hCcont : Continuous (fun α : ℝ => ∑ n ∈ Finset.range (2 * N), c n * e ((n : ℝ) * α)) :=
    expsum_continuous c (2 * N)
  have hEcont : Continuous (fun α : ℝ =>
      (∑ k ∈ Finset.range N, a k * e ((k : ℝ) * α)) ^ 2
        - ∑ n ∈ Finset.range (2 * N), c n * e ((n : ℝ) * α)) :=
    (hScont.pow 2).sub hCcont
  rw [variance_eq_L2_error a c N, L2_circle_split _ hEcont m hm hsub]
  have hminor : (∫ α in m,
      ‖(∑ k ∈ Finset.range N, a k * e ((k : ℝ) * α)) ^ 2
        - ∑ n ∈ Finset.range (2 * N), c n * e ((n : ℝ) * α)‖ ^ 2)
      ≤ 2 * (Csup ^ 2 * ∑ n ∈ Finset.range N, ‖a n‖ ^ 2)
        + 2 * ∑ n ∈ Finset.range (2 * N), ‖c n‖ ^ 2 := by
    have h1 := L2_diff_le _ _ (hScont.pow 2) hCcont m hm hsub
    have h2 := L4_set_bound a N m hm hsub Csup hsup
    have h3 : (∫ α in m, ‖∑ n ∈ Finset.range (2 * N), c n * e ((n : ℝ) * α)‖ ^ 2)
        ≤ ∑ n ∈ Finset.range (2 * N), ‖c n‖ ^ 2 := by
      calc (∫ α in m, ‖∑ n ∈ Finset.range (2 * N), c n * e ((n : ℝ) * α)‖ ^ 2)
          ≤ ∫ α in (0:ℝ)..1, ‖∑ n ∈ Finset.range (2 * N), c n * e ((n : ℝ) * α)‖ ^ 2 :=
            setL2_le_circle _ hCcont m hsub
        _ = ∑ n ∈ Finset.range (2 * N), ‖c n‖ ^ 2 := parseval c (2 * N)
    linarith
  linarith

open MeasureTheory in
/-- **Bessel's inequality on a sub-arc set**: the Fourier coefficients of `f` restricted
    to any measurable `m ⊆ (0,1]` satisfy `∑_{n<M} ‖∫_m f·e(−nα)‖² ≤ ∫_m ‖f‖²`.
    This is the lossless replacement for the crude main-term bound on minor arcs. -/
lemma bessel_minor (f : ℝ → ℂ) (hf : Continuous f) (m : Set ℝ)
    (hm : MeasurableSet m) (hsub : m ⊆ Set.Ioc (0:ℝ) 1) (M : ℕ) :
    ∑ n ∈ Finset.range M, ‖∫ α in m, f α * e (-((n : ℝ) * α))‖ ^ 2
      ≤ ∫ α in m, ‖f α‖ ^ 2 := by
  set c : ℕ → ℂ := fun n => ∫ α in m, f α * e (-((n : ℝ) * α)) with hc
  set T : ℝ → ℂ := fun α => ∑ n ∈ Finset.range M, c n * e ((n : ℝ) * α) with hT
  have hTcont : Continuous T := expsum_continuous c M
  have hecont : ∀ n : ℕ, Continuous fun α : ℝ => e (-((n : ℝ) * α)) := by
    intro n
    unfold e
    fun_prop
  -- integrability workhorses on m
  have hInt : ∀ g : ℝ → ℂ, Continuous g → IntegrableOn g m volume := fun g hg =>
    (hg.integrableOn_Ioc).mono_set hsub
  have hIntR : ∀ g : ℝ → ℝ, Continuous g → IntegrableOn g m volume := fun g hg =>
    (hg.integrableOn_Ioc).mono_set hsub
  -- Key 1: ∫_m f·conj T = ∑ c n · conj (c n)
  have hkey1 : (∫ α in m, f α * (starRingEnd ℂ) (T α))
      = ∑ n ∈ Finset.range M, c n * (starRingEnd ℂ) (c n) := by
    have hexp : ∀ α : ℝ, f α * (starRingEnd ℂ) (T α)
        = ∑ n ∈ Finset.range M, (starRingEnd ℂ) (c n) * (f α * e (-((n : ℝ) * α))) := by
      intro α
      rw [hT]
      dsimp only
      rw [map_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      rw [map_mul, e_conj]
      ring
    calc (∫ α in m, f α * (starRingEnd ℂ) (T α))
        = ∫ α in m, ∑ n ∈ Finset.range M, (starRingEnd ℂ) (c n) * (f α * e (-((n : ℝ) * α))) := by
          apply setIntegral_congr_fun hm
          intro α _
          exact hexp α
      _ = ∑ n ∈ Finset.range M, ∫ α in m, (starRingEnd ℂ) (c n) * (f α * e (-((n : ℝ) * α))) := by
          apply integral_finset_sum
          intro n _
          exact (hInt _ ((hf.mul (hecont n)).const_mul _))
      _ = ∑ n ∈ Finset.range M, (starRingEnd ℂ) (c n) * ∫ α in m, f α * e (-((n : ℝ) * α)) := by
          apply Finset.sum_congr rfl
          intro n _
          exact integral_const_mul _ _
      _ = ∑ n ∈ Finset.range M, c n * (starRingEnd ℂ) (c n) := by
          apply Finset.sum_congr rfl
          intro n _
          have hfold : (∫ α in m, f α * e (-((n : ℝ) * α))) = c n := rfl
          rw [hfold]
          ring
  -- Key 2: the expansion of ∫_m ‖f − T‖²
  have hptwise : ∀ α : ℝ, ‖f α - T α‖ ^ 2
      = ‖f α‖ ^ 2 - 2 * (f α * (starRingEnd ℂ) (T α)).re + ‖T α‖ ^ 2 := by
    intro α
    have h1 : (‖f α - T α‖ : ℝ) ^ 2 = ((f α - T α) * (starRingEnd ℂ) (f α - T α)).re := by
      rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    have h2 : (‖f α‖ : ℝ) ^ 2 = (f α * (starRingEnd ℂ) (f α)).re := by
      rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    have h3 : (‖T α‖ : ℝ) ^ 2 = (T α * (starRingEnd ℂ) (T α)).re := by
      rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    have hconjswap : (T α * (starRingEnd ℂ) (f α)).re = (f α * (starRingEnd ℂ) (T α)).re := by
      have : T α * (starRingEnd ℂ) (f α) = (starRingEnd ℂ) (f α * (starRingEnd ℂ) (T α)) := by
        rw [map_mul, Complex.conj_conj]
        ring
      rw [this, Complex.conj_re]
    rw [h1, h2, h3]
    have hexpand : (f α - T α) * (starRingEnd ℂ) (f α - T α)
        = f α * (starRingEnd ℂ) (f α) - f α * (starRingEnd ℂ) (T α)
          - T α * (starRingEnd ℂ) (f α) + T α * (starRingEnd ℂ) (T α) := by
      rw [map_sub]
      ring
    rw [hexpand]
    simp only [Complex.add_re, Complex.sub_re]
    rw [hconjswap]
    ring
  have hIfT : IntegrableOn (fun α => (f α * (starRingEnd ℂ) (T α)).re) m volume := by
    apply hIntR
    exact (Complex.continuous_re.comp (hf.mul (Complex.continuous_conj.comp hTcont)))
  have hIf2 : IntegrableOn (fun α => ‖f α‖ ^ 2) m volume := hIntR _ (hf.norm.pow 2)
  have hIT2 : IntegrableOn (fun α => ‖T α‖ ^ 2) m volume := hIntR _ (hTcont.norm.pow 2)
  have hkey2 : (∫ α in m, ‖f α - T α‖ ^ 2)
      = (∫ α in m, ‖f α‖ ^ 2) - 2 * (∫ α in m, f α * (starRingEnd ℂ) (T α)).re
        + ∫ α in m, ‖T α‖ ^ 2 := by
    have hre : (∫ α in m, (f α * (starRingEnd ℂ) (T α)).re)
        = (∫ α in m, f α * (starRingEnd ℂ) (T α)).re := by
      have h := integral_re (hInt (fun α => f α * (starRingEnd ℂ) (T α))
        (hf.mul (Complex.continuous_conj.comp hTcont)))
      simpa [RCLike.re_to_complex] using h
    calc (∫ α in m, ‖f α - T α‖ ^ 2)
        = ∫ α in m, (‖f α‖ ^ 2 - 2 * (f α * (starRingEnd ℂ) (T α)).re + ‖T α‖ ^ 2) := by
          apply setIntegral_congr_fun hm
          intro α _
          exact hptwise α
      _ = (∫ α in m, (‖f α‖ ^ 2 - 2 * (f α * (starRingEnd ℂ) (T α)).re))
          + ∫ α in m, ‖T α‖ ^ 2 := by
          apply integral_add _ hIT2
          exact hIf2.sub (hIfT.const_mul 2)
      _ = (∫ α in m, ‖f α‖ ^ 2) - (∫ α in m, 2 * (f α * (starRingEnd ℂ) (T α)).re)
          + ∫ α in m, ‖T α‖ ^ 2 := by
          rw [integral_sub hIf2 (hIfT.const_mul 2)]
      _ = (∫ α in m, ‖f α‖ ^ 2) - 2 * (∫ α in m, f α * (starRingEnd ℂ) (T α)).re
          + ∫ α in m, ‖T α‖ ^ 2 := by
          rw [integral_const_mul, hre]
  -- Key 3: ∫_m ‖T‖² ≤ ∑ ‖c n‖²
  have hkey3 : (∫ α in m, ‖T α‖ ^ 2) ≤ ∑ n ∈ Finset.range M, ‖c n‖ ^ 2 := by
    calc (∫ α in m, ‖T α‖ ^ 2) ≤ ∫ α in (0:ℝ)..1, ‖T α‖ ^ 2 :=
          setL2_le_circle T hTcont m hsub
      _ = ∑ n ∈ Finset.range M, ‖c n‖ ^ 2 := parseval c M
  -- the cross term is the coefficient mass
  have hcross : (∫ α in m, f α * (starRingEnd ℂ) (T α)).re
      = ∑ n ∈ Finset.range M, ‖c n‖ ^ 2 := by
    rw [hkey1]
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro n _
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  -- combine: 0 ≤ ∫‖f−T‖² = ∫‖f‖² − 2∑‖c‖² + ∫_m‖T‖² ≤ ∫‖f‖² − ∑‖c‖²
  have hnonneg : (0:ℝ) ≤ ∫ α in m, ‖f α - T α‖ ^ 2 := by
    apply integral_nonneg
    intro α
    positivity
  rw [hkey2, hcross] at hnonneg
  linarith [hkey3]

open MeasureTheory in
/-- Splitting a continuous complex integrand over the circle into a sub-arc set and its
    complement. -/
lemma integral_circle_split (g : ℝ → ℂ) (hg : Continuous g) (m : Set ℝ)
    (hm : MeasurableSet m) (hsub : m ⊆ Set.Ioc (0:ℝ) 1) :
    ∫ α in (0:ℝ)..1, g α
      = (∫ α in m, g α) + ∫ α in Set.Ioc (0:ℝ) 1 \ m, g α := by
  have hi : IntegrableOn g (Set.Ioc (0:ℝ) 1) volume := hg.integrableOn_Ioc
  rw [intervalIntegral.integral_of_le zero_le_one,
    ← setIntegral_union Set.disjoint_sdiff_right (measurableSet_Ioc.diff hm)
      (hi.mono_set hsub) (hi.mono_set Set.diff_subset),
    Set.union_diff_cancel hsub]

open MeasureTheory in
/-- **The lossless variance assembly**: the variance against ANY main term `c` is at most
    twice the minor-arc L⁴ integral plus twice the major-arc coefficient error — with NO
    loss on the main term (Bessel replaces the crude full-circle Parseval bound). The
    second sum is exactly the Siegel–Walfisz-grade object. -/
theorem variance_le_bessel (a : ℕ → ℂ) (N : ℕ) (m : Set ℝ) (hm : MeasurableSet m)
    (hsub : m ⊆ Set.Ioc (0:ℝ) 1) (c : ℕ → ℂ) :
    ∑ n ∈ Finset.range (2 * N),
        ‖(∑ p ∈ (Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 = n),
            a p.1 * a p.2) - c n‖ ^ 2
      ≤ 2 * (∫ α in m, ‖∑ k ∈ Finset.range N, a k * e ((k : ℝ) * α)‖ ^ 4)
        + 2 * ∑ n ∈ Finset.range (2 * N),
            ‖(∫ α in Set.Ioc (0:ℝ) 1 \ m,
                (∑ k ∈ Finset.range N, a k * e ((k : ℝ) * α)) ^ 2 * e (-((n : ℝ) * α)))
              - c n‖ ^ 2 := by
  set S : ℝ → ℂ := fun α => ∑ k ∈ Finset.range N, a k * e ((k : ℝ) * α) with hS
  have hScont : Continuous S := expsum_continuous a N
  have hS2cont : Continuous (fun α => S α ^ 2) := hScont.pow 2
  have hgcont : ∀ n : ℕ, Continuous (fun α => S α ^ 2 * e (-((n : ℝ) * α))) := by
    intro n
    apply hS2cont.mul
    unfold e
    fun_prop
  -- coefficient split: R(n) = minor coefficient + major coefficient
  have hsplitn : ∀ n : ℕ,
      (∑ p ∈ (Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 = n),
        a p.1 * a p.2)
      = (∫ α in m, S α ^ 2 * e (-((n : ℝ) * α)))
        + ∫ α in Set.Ioc (0:ℝ) 1 \ m, S α ^ 2 * e (-((n : ℝ) * α)) := by
    intro n
    rw [← fourier_coeff_sq a N n]
    exact integral_circle_split _ (hgcont n) m hm hsub
  -- pointwise: ‖x + y − c‖² ≤ 2‖x‖² + 2‖y − c‖²
  have hpt : ∀ n ∈ Finset.range (2 * N),
      ‖(∑ p ∈ (Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 = n),
          a p.1 * a p.2) - c n‖ ^ 2
      ≤ 2 * ‖∫ α in m, S α ^ 2 * e (-((n : ℝ) * α))‖ ^ 2
        + 2 * ‖(∫ α in Set.Ioc (0:ℝ) 1 \ m, S α ^ 2 * e (-((n : ℝ) * α))) - c n‖ ^ 2 := by
    intro n _
    rw [hsplitn n]
    set x := ∫ α in m, S α ^ 2 * e (-((n : ℝ) * α))
    set y := (∫ α in Set.Ioc (0:ℝ) 1 \ m, S α ^ 2 * e (-((n : ℝ) * α))) - c n
    have hxy : x + (∫ α in Set.Ioc (0:ℝ) 1 \ m, S α ^ 2 * e (-((n : ℝ) * α))) - c n
        = x + y := by ring
    rw [hxy]
    have htri : ‖x + y‖ ≤ ‖x‖ + ‖y‖ := norm_add_le x y
    have hsq : ‖x + y‖ ^ 2 ≤ (‖x‖ + ‖y‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) htri 2
    nlinarith [sq_nonneg (‖x‖ - ‖y‖), norm_nonneg x, norm_nonneg y]
  -- sum up and apply Bessel to the minor coefficients
  have hbessel : ∑ n ∈ Finset.range (2 * N),
      ‖∫ α in m, S α ^ 2 * e (-((n : ℝ) * α))‖ ^ 2
      ≤ ∫ α in m, ‖S α‖ ^ 4 := by
    have hb := bessel_minor (fun α => S α ^ 2) hS2cont m hm hsub (2 * N)
    calc ∑ n ∈ Finset.range (2 * N), ‖∫ α in m, S α ^ 2 * e (-((n : ℝ) * α))‖ ^ 2
        ≤ ∫ α in m, ‖S α ^ 2‖ ^ 2 := hb
      _ = ∫ α in m, ‖S α‖ ^ 4 := by
          apply setIntegral_congr_fun hm
          intro α _
          dsimp only
          rw [norm_pow, ← pow_mul]
  calc ∑ n ∈ Finset.range (2 * N),
        ‖(∑ p ∈ (Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 = n),
            a p.1 * a p.2) - c n‖ ^ 2
      ≤ ∑ n ∈ Finset.range (2 * N),
          (2 * ‖∫ α in m, S α ^ 2 * e (-((n : ℝ) * α))‖ ^ 2
            + 2 * ‖(∫ α in Set.Ioc (0:ℝ) 1 \ m, S α ^ 2 * e (-((n : ℝ) * α))) - c n‖ ^ 2) :=
        Finset.sum_le_sum hpt
    _ = 2 * (∑ n ∈ Finset.range (2 * N),
            ‖∫ α in m, S α ^ 2 * e (-((n : ℝ) * α))‖ ^ 2)
        + 2 * ∑ n ∈ Finset.range (2 * N),
            ‖(∫ α in Set.Ioc (0:ℝ) 1 \ m, S α ^ 2 * e (-((n : ℝ) * α))) - c n‖ ^ 2 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ 2 * (∫ α in m, ‖S α‖ ^ 4)
        + 2 * ∑ n ∈ Finset.range (2 * N),
            ‖(∫ α in Set.Ioc (0:ℝ) 1 \ m, S α ^ 2 * e (-((n : ℝ) * α))) - c n‖ ^ 2 := by
        have h2 : (0:ℝ) ≤ 2 := by norm_num
        linarith [mul_le_mul_of_nonneg_left hbessel h2]

/-- **Major-arc residue decomposition** — the entry point of the major-arc evaluation:
    at `α = a/q + β`, any weighted exponential sum regroups into the `q` residue classes,
    `∑ g(n)e(nα) = ∑_{r<q} e(ra/q)·∑_{n≡r(q)} g(n)e(nβ)` — reducing the window evaluation
    to AP-restricted sums (the `WeakPNT_AP` shape) twisted by the smooth `e(nβ)`. -/
lemma major_arc_residue_decomp (g : ℕ → ℂ) (N : ℕ) (a : ℤ) (q : ℕ) (hq : 0 < q) (β : ℝ) :
    ∑ n ∈ Finset.range N, g n * e ((n : ℝ) * ((a : ℝ) / (q : ℝ) + β))
      = ∑ r ∈ Finset.range q, e ((r : ℝ) * (a : ℝ) / (q : ℝ))
          * ∑ n ∈ (Finset.range N).filter (fun n => n % q = r), g n * e ((n : ℝ) * β) := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun n => n % q) (t := Finset.range q)
      (fun n _ => Finset.mem_range.mpr (Nat.mod_lt n hq))]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.mem_filter] at hn
  obtain ⟨-, hr⟩ := hn
  have hq' : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  have hn_nat : q * (n / q) + r = n := by
    rw [← hr]
    exact Nat.div_add_mod n q
  have hn_eq : (n : ℝ) = (q : ℝ) * ((n / q : ℕ) : ℝ) + (r : ℝ) := by
    exact_mod_cast hn_nat.symm
  have key : (n : ℝ) * ((a : ℝ) / (q : ℝ))
      = ((a * (n / q : ℕ) : ℤ) : ℝ) + (r : ℝ) * (a : ℝ) / (q : ℝ) := by
    rw [hn_eq, Int.cast_mul, Int.cast_natCast]
    field_simp
  have hdecomp : (n : ℝ) * ((a : ℝ) / (q : ℝ) + β)
      = ((a * (n / q : ℕ) : ℤ) : ℝ) + ((r : ℝ) * (a : ℝ) / (q : ℝ) + (n : ℝ) * β) := by
    calc (n : ℝ) * ((a : ℝ) / (q : ℝ) + β)
        = (n : ℝ) * ((a : ℝ) / (q : ℝ)) + (n : ℝ) * β := by ring
      _ = (((a * (n / q : ℕ) : ℤ) : ℝ) + (r : ℝ) * (a : ℝ) / (q : ℝ)) + (n : ℝ) * β := by
          rw [key]
      _ = ((a * (n / q : ℕ) : ℤ) : ℝ) + ((r : ℝ) * (a : ℝ) / (q : ℝ) + (n : ℝ) * β) := by
          ring
  calc g n * e ((n : ℝ) * ((a : ℝ) / (q : ℝ) + β))
      = g n * e (((a * (n / q : ℕ) : ℤ) : ℝ)
          + ((r : ℝ) * (a : ℝ) / (q : ℝ) + (n : ℝ) * β)) := by rw [hdecomp]
    _ = g n * (e (((a * (n / q : ℕ) : ℤ) : ℝ))
          * e ((r : ℝ) * (a : ℝ) / (q : ℝ) + (n : ℝ) * β)) := by rw [e_add]
    _ = g n * e ((r : ℝ) * (a : ℝ) / (q : ℝ) + (n : ℝ) * β) := by
        rw [e_int]
        ring
    _ = g n * (e ((r : ℝ) * (a : ℝ) / (q : ℝ)) * e ((n : ℝ) * β)) := by rw [e_add]
    _ = e ((r : ℝ) * (a : ℝ) / (q : ℝ)) * (g n * e ((n : ℝ) * β)) := by ring

/-- **Abel bound for a twisted sum**: if all partial sums of `a` are `≤ B` in norm, the
    `e(nβ)`-twisted sum is `≤ B(1 + 2πN|β|)` — the summation-by-parts step that converts
    `WeakPNT_AP`-style partial-sum control into major-arc window evaluations, with the
    window factor `N|β| = O(P)` bounded on a Farey arc. -/
lemma abel_twisted_error (a : ℕ → ℂ) (β : ℝ) (N : ℕ) (B : ℝ)
    (hB : ∀ t ≤ N, ‖∑ n ∈ Finset.range t, a n‖ ≤ B) :
    ‖∑ n ∈ Finset.range N, a n * e ((n : ℝ) * β)‖
      ≤ B * (1 + 2 * Real.pi * N * |β|) := by
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0 (Nat.zero_le N))
  have hfac : (0:ℝ) ≤ 2 * Real.pi * N * |β| := by positivity
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · subst hN0
    simp only [Finset.range_zero, Finset.sum_empty, norm_zero]
    exact mul_nonneg hB0 (by linarith)
  have hstep : ∀ i : ℕ, ‖e (((i + 1 : ℕ) : ℝ) * β) - e ((i : ℝ) * β)‖
      ≤ 2 * Real.pi * |β| := by
    intro i
    have hfact : e (((i + 1 : ℕ) : ℝ) * β) - e ((i : ℝ) * β)
        = e ((i : ℝ) * β) * (e β - 1) := by
      rw [mul_sub, mul_one, e_add]
      congr 1
      push_cast
      ring
    rw [hfact, norm_mul, e_norm, one_mul, e_sub_one_norm]
    have hsin := Real.abs_sin_le_abs (x := Real.pi * β)
    have hpi : |Real.pi * β| = Real.pi * |β| := by
      rw [abs_mul, abs_of_pos Real.pi_pos]
    linarith [hsin, hpi.le, hpi.ge]
  have habel : ∑ n ∈ Finset.range N, a n * e ((n : ℝ) * β)
      = e (((N - 1 : ℕ) : ℝ) * β) * (∑ n ∈ Finset.range N, a n)
        - ∑ i ∈ Finset.range (N - 1),
            (e (((i + 1 : ℕ) : ℝ) * β) - e ((i : ℝ) * β)) * ∑ j ∈ Finset.range (i + 1), a j := by
    have h := Finset.sum_range_by_parts (f := fun m : ℕ => e ((m : ℝ) * β)) (g := a) (n := N)
    simp only [smul_eq_mul] at h
    calc ∑ n ∈ Finset.range N, a n * e ((n : ℝ) * β)
        = ∑ n ∈ Finset.range N, e ((n : ℝ) * β) * a n := by
          apply Finset.sum_congr rfl
          intro n _
          ring
      _ = _ := h
  rw [habel]
  calc ‖e (((N - 1 : ℕ) : ℝ) * β) * (∑ n ∈ Finset.range N, a n)
        - ∑ i ∈ Finset.range (N - 1),
            (e (((i + 1 : ℕ) : ℝ) * β) - e ((i : ℝ) * β)) * ∑ j ∈ Finset.range (i + 1), a j‖
      ≤ ‖e (((N - 1 : ℕ) : ℝ) * β) * (∑ n ∈ Finset.range N, a n)‖
        + ‖∑ i ∈ Finset.range (N - 1),
            (e (((i + 1 : ℕ) : ℝ) * β) - e ((i : ℝ) * β)) * ∑ j ∈ Finset.range (i + 1), a j‖ :=
        norm_sub_le _ _
    _ ≤ B + ((N - 1 : ℕ) : ℝ) * (2 * Real.pi * |β| * B) := by
        apply add_le_add
        · rw [norm_mul, e_norm, one_mul]
          exact hB N le_rfl
        · calc ‖∑ i ∈ Finset.range (N - 1),
              (e (((i + 1 : ℕ) : ℝ) * β) - e ((i : ℝ) * β)) * ∑ j ∈ Finset.range (i + 1), a j‖
              ≤ ∑ i ∈ Finset.range (N - 1),
                ‖(e (((i + 1 : ℕ) : ℝ) * β) - e ((i : ℝ) * β)) * ∑ j ∈ Finset.range (i + 1), a j‖ :=
                norm_sum_le _ _
            _ ≤ ∑ _i ∈ Finset.range (N - 1), 2 * Real.pi * |β| * B := by
                apply Finset.sum_le_sum
                intro i hi
                rw [norm_mul]
                apply mul_le_mul (hstep i) (hB (i + 1) ?_) (norm_nonneg _) (by positivity)
                rw [Finset.mem_range] at hi
                omega
            _ = ((N - 1 : ℕ) : ℝ) * (2 * Real.pi * |β| * B) := by
                rw [Finset.sum_const, nsmul_eq_mul, Finset.card_range]
    _ ≤ B * (1 + 2 * Real.pi * N * |β|) := by
        have hle : ((N - 1 : ℕ) : ℝ) ≤ (N : ℝ) := by
          exact_mod_cast Nat.sub_le N 1
        have hnn : (0:ℝ) ≤ 2 * Real.pi * |β| := by positivity
        nlinarith [hB0, hnn, hle, mul_le_mul_of_nonneg_right hle hnn]

/-- **AP window sum vs smooth model**: if the residue-class partial sums of `g` track the
    linear model `t·κ` within `B` (the `WeakPNT_AP` error shape with `κ = 1/φ(q)`), then
    the twisted window sum tracks `κ·∑e(nβ)` within `B(1 + 2πN|β|)`. With
    `major_arc_residue_decomp` this evaluates `S` on a whole Farey window. -/
lemma ap_twisted_model (g : ℕ → ℂ) (κ : ℂ) (q r N : ℕ) (β : ℝ) (B : ℝ)
    (hB : ∀ t ≤ N, ‖(∑ n ∈ (Finset.range t).filter (fun n => n % q = r), g n)
        - (t : ℂ) * κ‖ ≤ B) :
    ‖(∑ n ∈ (Finset.range N).filter (fun n => n % q = r), g n * e ((n : ℝ) * β))
      - κ * ∑ n ∈ Finset.range N, e ((n : ℝ) * β)‖
      ≤ B * (1 + 2 * Real.pi * N * |β|) := by
  set a : ℕ → ℂ := fun n => (if n % q = r then g n else 0) - κ with ha
  have hpartial : ∀ t : ℕ, ∑ n ∈ Finset.range t, a n
      = (∑ n ∈ (Finset.range t).filter (fun n => n % q = r), g n) - (t : ℂ) * κ := by
    intro t
    rw [ha]
    rw [Finset.sum_sub_distrib, Finset.sum_ite, Finset.sum_const_zero, add_zero,
      Finset.sum_const, Finset.card_range]
    simp [nsmul_eq_mul]
  have htwist : ∑ n ∈ Finset.range N, a n * e ((n : ℝ) * β)
      = (∑ n ∈ (Finset.range N).filter (fun n => n % q = r), g n * e ((n : ℝ) * β))
        - κ * ∑ n ∈ Finset.range N, e ((n : ℝ) * β) := by
    rw [ha]
    have hterm : ∀ n : ℕ, ((if n % q = r then g n else 0) - κ) * e ((n : ℝ) * β)
        = (if n % q = r then g n * e ((n : ℝ) * β) else 0) - κ * e ((n : ℝ) * β) := by
      intro n
      by_cases h : n % q = r
      · rw [if_pos h, if_pos h]
        ring
      · rw [if_neg h, if_neg h]
        ring
    calc ∑ n ∈ Finset.range N, ((if n % q = r then g n else 0) - κ) * e ((n : ℝ) * β)
        = ∑ n ∈ Finset.range N,
            ((if n % q = r then g n * e ((n : ℝ) * β) else 0) - κ * e ((n : ℝ) * β)) := by
          apply Finset.sum_congr rfl
          intro n _
          exact hterm n
      _ = (∑ n ∈ Finset.range N, if n % q = r then g n * e ((n : ℝ) * β) else 0)
          - ∑ n ∈ Finset.range N, κ * e ((n : ℝ) * β) := by
          rw [Finset.sum_sub_distrib]
      _ = (∑ n ∈ (Finset.range N).filter (fun n => n % q = r), g n * e ((n : ℝ) * β))
          - κ * ∑ n ∈ Finset.range N, e ((n : ℝ) * β) := by
          rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.mul_sum]
  rw [← htwist]
  apply abel_twisted_error
  intro t ht
  rw [hpartial t]
  exact hB t ht

/-- **Cesàro limit to window bound**: if `(∑_{n<t} c(n))/t → κ`, then for every `ε > 0`
    there is a constant `C` with `‖∑_{n<t} c(n) − tκ‖ ≤ εN + C` for ALL `t ≤ N` — the
    exact `B` that `ap_twisted_model` consumes. Converts `WeakPNT_AP`'s Tendsto into
    per-window control, with the small-`t` range absorbed into `C`. -/
lemma partial_sum_window_bound (c : ℕ → ℂ) (κ : ℂ)
    (h : Filter.Tendsto (fun t : ℕ => (∑ n ∈ Finset.range t, c n) / (t : ℂ))
      Filter.atTop (nhds κ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, ∀ t ≤ N,
      ‖(∑ n ∈ Finset.range t, c n) - (t : ℂ) * κ‖ ≤ ε * N + C := by
  have hev : ∀ᶠ t : ℕ in Filter.atTop,
      ‖(∑ n ∈ Finset.range t, c n) / (t : ℂ) - κ‖ < ε := by
    have := Metric.tendsto_nhds.mp h ε hε
    simpa [dist_eq_norm] using this
  obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.mp hev
  refine ⟨(∑ n ∈ Finset.range T₀, ‖c n‖) + T₀ * ‖κ‖, by positivity, ?_⟩
  intro N t htN
  have hNnn : (0:ℝ) ≤ ε * N := by positivity
  rcases Nat.eq_zero_or_pos t with rfl | ht0
  · simp only [Finset.range_zero, Finset.sum_empty, Nat.cast_zero, zero_mul, sub_zero,
      norm_zero]
    positivity
  by_cases hT : T₀ ≤ t
  · have h1 := hT₀ t hT
    have hne : ((t : ℕ) : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
    have hfact : (∑ n ∈ Finset.range t, c n) - (t : ℂ) * κ
        = (t : ℂ) * ((∑ n ∈ Finset.range t, c n) / (t : ℂ) - κ) := by
      field_simp
    rw [hfact, norm_mul, Complex.norm_natCast]
    have htN' : (t : ℝ) ≤ (N : ℝ) := by exact_mod_cast htN
    calc (t : ℝ) * ‖(∑ n ∈ Finset.range t, c n) / (t : ℂ) - κ‖
        ≤ (t : ℝ) * ε := mul_le_mul_of_nonneg_left h1.le (Nat.cast_nonneg t)
      _ ≤ (N : ℝ) * ε := mul_le_mul_of_nonneg_right htN' hε.le
      _ = ε * N := by ring
      _ ≤ ε * N + ((∑ n ∈ Finset.range T₀, ‖c n‖) + T₀ * ‖κ‖) := by
          have hCnn : (0:ℝ) ≤ (∑ n ∈ Finset.range T₀, ‖c n‖) + T₀ * ‖κ‖ := by positivity
          linarith
  · push_neg at hT
    calc ‖(∑ n ∈ Finset.range t, c n) - (t : ℂ) * κ‖
        ≤ ‖∑ n ∈ Finset.range t, c n‖ + ‖(t : ℂ) * κ‖ := norm_sub_le _ _
      _ ≤ (∑ n ∈ Finset.range t, ‖c n‖) + (t : ℝ) * ‖κ‖ := by
          apply add_le_add (norm_sum_le _ _)
          rw [norm_mul, Complex.norm_natCast]
      _ ≤ (∑ n ∈ Finset.range T₀, ‖c n‖) + (T₀ : ℝ) * ‖κ‖ := by
          apply add_le_add
          · apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro x hx
              rw [Finset.mem_range] at hx ⊢
              omega
            · intro n _ _
              exact norm_nonneg _
          · apply mul_le_mul_of_nonneg_right _ (norm_nonneg κ)
            exact_mod_cast hT.le
      _ ≤ ε * N + ((∑ n ∈ Finset.range T₀, ‖c n‖) + T₀ * ‖κ‖) := by linarith

/-- **The window evaluation** (route-1 capstone): if each residue class of `g` has Cesàro
    density `κ(r)` (the `WeakPNT_AP` shape for each FIXED `q`), then for every `ε > 0`
    there is `C` such that on EVERY window `a/q + β`,
    `‖S − (∑_r e(ra/q)κ(r))·∑e(nβ)‖ ≤ q(εN+C)(1+2πN|β|)` — with `N|β| = O(P)` bounded on
    a Farey arc, this is `o(N)` per window with NO uniformity in `q`. -/
theorem major_window_eval (g : ℕ → ℂ) (q : ℕ) (hq : 0 < q) (κ : ℕ → ℂ)
    (hκ : ∀ r, r < q → Filter.Tendsto
      (fun t : ℕ => (∑ n ∈ (Finset.range t).filter (fun n => n % q = r), g n) / (t : ℂ))
      Filter.atTop (nhds (κ r)))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, ∀ a : ℤ, ∀ β : ℝ,
      ‖(∑ n ∈ Finset.range N, g n * e ((n : ℝ) * ((a : ℝ) / (q : ℝ) + β)))
        - (∑ r ∈ Finset.range q, e ((r : ℝ) * (a : ℝ) / (q : ℝ)) * κ r)
          * ∑ n ∈ Finset.range N, e ((n : ℝ) * β)‖
      ≤ (q : ℝ) * ((ε * N + C) * (1 + 2 * Real.pi * N * |β|)) := by
  classical
  -- per-residue constants from the extractor
  have hres : ∀ r, r < q → ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, ∀ t ≤ N,
      ‖(∑ n ∈ (Finset.range t).filter (fun n => n % q = r), g n) - (t : ℂ) * κ r‖
        ≤ ε * N + C := by
    intro r hr
    have hconv : (fun t : ℕ => (∑ n ∈ Finset.range t,
          if n % q = r then g n else 0) / (t : ℂ))
        = (fun t : ℕ => (∑ n ∈ (Finset.range t).filter (fun n => n % q = r), g n) / (t : ℂ)) := by
      funext t
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
    obtain ⟨C, hC0, hC⟩ := partial_sum_window_bound
      (fun n => if n % q = r then g n else 0) (κ r) (by rw [hconv]; exact hκ r hr) ε hε
    refine ⟨C, hC0, fun N t ht => ?_⟩
    have := hC N t ht
    rwa [Finset.sum_ite, Finset.sum_const_zero, add_zero] at this
  -- a single constant dominating all residues
  set Cf : ℕ → ℝ := fun r => if h : r < q then (hres r h).choose else 0 with hCf
  set Ctot : ℝ := ∑ r ∈ Finset.range q, Cf r with hCtot
  have hCf0 : ∀ r, 0 ≤ Cf r := by
    intro r
    by_cases h : r < q
    · simp only [hCf, dif_pos h]
      exact (hres r h).choose_spec.1
    · simp only [hCf, dif_neg h]
      exact le_refl 0
  have hCtot0 : 0 ≤ Ctot := Finset.sum_nonneg fun r _ => hCf0 r
  have hCfle : ∀ r ∈ Finset.range q, Cf r ≤ Ctot := by
    intro r hr
    exact Finset.single_le_sum (fun i _ => hCf0 i) hr
  refine ⟨Ctot, hCtot0, fun N a β => ?_⟩
  rw [major_arc_residue_decomp g N a q hq β, Finset.sum_mul, ← Finset.sum_sub_distrib]
  have hfac : (0:ℝ) ≤ 1 + 2 * Real.pi * N * |β| := by positivity
  calc ‖∑ r ∈ Finset.range q,
        (e ((r : ℝ) * (a : ℝ) / (q : ℝ))
            * ∑ n ∈ (Finset.range N).filter (fun n => n % q = r), g n * e ((n : ℝ) * β)
          - e ((r : ℝ) * (a : ℝ) / (q : ℝ)) * κ r * ∑ n ∈ Finset.range N, e ((n : ℝ) * β))‖
      ≤ ∑ r ∈ Finset.range q,
        ‖e ((r : ℝ) * (a : ℝ) / (q : ℝ))
            * ∑ n ∈ (Finset.range N).filter (fun n => n % q = r), g n * e ((n : ℝ) * β)
          - e ((r : ℝ) * (a : ℝ) / (q : ℝ)) * κ r * ∑ n ∈ Finset.range N, e ((n : ℝ) * β)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _r ∈ Finset.range q, (ε * N + Ctot) * (1 + 2 * Real.pi * N * |β|) := by
        apply Finset.sum_le_sum
        intro r hr
        have hrq : r < q := Finset.mem_range.mp hr
        have hfactor : e ((r : ℝ) * (a : ℝ) / (q : ℝ))
              * ∑ n ∈ (Finset.range N).filter (fun n => n % q = r), g n * e ((n : ℝ) * β)
            - e ((r : ℝ) * (a : ℝ) / (q : ℝ)) * κ r * ∑ n ∈ Finset.range N, e ((n : ℝ) * β)
            = e ((r : ℝ) * (a : ℝ) / (q : ℝ))
              * ((∑ n ∈ (Finset.range N).filter (fun n => n % q = r), g n * e ((n : ℝ) * β))
                - κ r * ∑ n ∈ Finset.range N, e ((n : ℝ) * β)) := by
          ring
        rw [hfactor, norm_mul, e_norm, one_mul]
        have hB : ∀ t ≤ N,
            ‖(∑ n ∈ (Finset.range t).filter (fun n => n % q = r), g n) - (t : ℂ) * κ r‖
              ≤ ε * N + Ctot := by
          intro t ht
          have h1 := (hres r hrq).choose_spec.2 N t ht
          have h2 : Cf r = (hres r hrq).choose := by
            simp only [hCf, dif_pos hrq]
          have h3 := hCfle r hr
          rw [h2] at h3
          linarith
        exact ap_twisted_model g (κ r) q r N β (ε * N + Ctot) hB
    _ = (q : ℝ) * ((ε * N + Ctot) * (1 + 2 * Real.pi * N * |β|)) := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_range]

/-- **Squaring a window estimate**: `‖S−M‖ ≤ E ⟹ ‖S²−M²‖ ≤ E(E+2‖M‖)` — converts the
    window evaluation of `S` into the window evaluation of `S²` that the major
    coefficient `∫_𝔐 S²e(−nα)` consumes. -/
lemma sq_diff_norm_le (S M : ℂ) (E : ℝ) (h : ‖S - M‖ ≤ E) :
    ‖S ^ 2 - M ^ 2‖ ≤ E * (E + 2 * ‖M‖) := by
  have hE0 : 0 ≤ E := le_trans (norm_nonneg _) h
  have hfact : S ^ 2 - M ^ 2 = (S - M) * ((S - M) + 2 * M) := by ring
  rw [hfact, norm_mul]
  apply mul_le_mul h _ (norm_nonneg _) hE0
  calc ‖(S - M) + 2 * M‖ ≤ ‖S - M‖ + ‖(2 : ℂ) * M‖ := norm_add_le _ _
    _ ≤ E + 2 * ‖M‖ := by
        rw [norm_mul]
        have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
        rw [h2]
        linarith

open ArithmeticFunction in
/-- **Ramanujan sum at coprime argument**: `∑_{r<q, gcd(r,q)=1} e(ar/q) = μ(q)` —
    the arithmetic heart of the singular series. Möbius inclusion-exclusion over the
    banked additive-character orthogonality. -/
lemma ramanujan_sum_coprime (a : ℤ) (q : ℕ) (hq : 0 < q) (ha : Int.gcd a q = 1) :
    ∑ r ∈ (Finset.range q).filter (fun r => Nat.gcd r q = 1), e ((a : ℝ) * r / q)
      = (ArithmeticFunction.moebius q : ℂ) := by
  classical
  have hq' : q ≠ 0 := hq.ne'
  have hind : ∀ n : ℕ, n ≠ 0 →
      (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℂ)) = if n = 1 then 1 else 0 := by
    intro n hn
    have h : ((ArithmeticFunction.moebius * ArithmeticFunction.zeta :
        ArithmeticFunction ℤ)) n = (1 : ArithmeticFunction ℤ) n := by
      rw [ArithmeticFunction.moebius_mul_coe_zeta]
    rw [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
    by_cases h1 : n = 1
    · rw [if_pos h1, h1]
      simp
    · rw [if_neg h1]
      rw [if_neg h1] at h
      have : ((∑ d ∈ n.divisors, ArithmeticFunction.moebius d : ℤ) : ℂ) = 0 := by
        rw [h]
        norm_num
      push_cast at this
      exact this
  have hdivset : ∀ r : ℕ, (Nat.gcd r q).divisors = q.divisors.filter (fun d => d ∣ r) := by
    intro r
    ext d
    simp only [Nat.mem_divisors, Finset.mem_filter]
    constructor
    · rintro ⟨hdvd, -⟩
      rw [Nat.dvd_gcd_iff] at hdvd
      exact ⟨⟨hdvd.2, hq'⟩, hdvd.1⟩
    · rintro ⟨⟨hdq, -⟩, hdr⟩
      exact ⟨Nat.dvd_gcd hdr hdq, fun hc => hq' (Nat.gcd_eq_zero_iff.mp hc).2⟩
  have hstep : ∑ r ∈ (Finset.range q).filter (fun r => Nat.gcd r q = 1), e ((a : ℝ) * r / q)
      = ∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℂ)
          * ∑ r ∈ (Finset.range q).filter (fun r => d ∣ r), e ((a : ℝ) * r / q) := by
    rw [Finset.sum_filter]
    have hpt : ∀ r ∈ Finset.range q,
        (if Nat.gcd r q = 1 then e ((a : ℝ) * r / q) else 0)
        = ∑ d ∈ q.divisors, if d ∣ r then (ArithmeticFunction.moebius d : ℂ)
            * e ((a : ℝ) * r / q) else 0 := by
      intro r _
      have hgpos : Nat.gcd r q ≠ 0 := fun hc => hq' (Nat.gcd_eq_zero_iff.mp hc).2
      calc (if Nat.gcd r q = 1 then e ((a : ℝ) * r / q) else 0)
          = (if Nat.gcd r q = 1 then (1:ℂ) else 0) * e ((a : ℝ) * r / q) := by
            by_cases h : Nat.gcd r q = 1
            · rw [if_pos h, if_pos h, one_mul]
            · rw [if_neg h, if_neg h, zero_mul]
        _ = (∑ d ∈ (Nat.gcd r q).divisors, (ArithmeticFunction.moebius d : ℂ))
              * e ((a : ℝ) * r / q) := by rw [hind _ hgpos]
        _ = ∑ d ∈ q.divisors.filter (fun d => d ∣ r),
              (ArithmeticFunction.moebius d : ℂ) * e ((a : ℝ) * r / q) := by
            rw [hdivset r, Finset.sum_mul]
        _ = ∑ d ∈ q.divisors, if d ∣ r then (ArithmeticFunction.moebius d : ℂ)
              * e ((a : ℝ) * r / q) else 0 := by
            rw [Finset.sum_filter]
    rw [Finset.sum_congr rfl hpt, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro d _
    rw [Finset.mul_sum, Finset.sum_filter]
  have hinner : ∀ d ∈ q.divisors,
      (∑ r ∈ (Finset.range q).filter (fun r => d ∣ r), e ((a : ℝ) * r / q))
      = if ((q / d : ℕ) : ℤ) ∣ a then ((q / d : ℕ) : ℂ) else 0 := by
    intro d hd
    rw [Nat.mem_divisors] at hd
    obtain ⟨hdq, -⟩ := hd
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdq hq
    have hm0 : q / d ≠ 0 := (Nat.div_pos (Nat.le_of_dvd hq hdq) hd0).ne'
    have hqe : d * (q / d) = q := Nat.mul_div_cancel' hdq
    have hreindex : (∑ r ∈ (Finset.range q).filter (fun r => d ∣ r), e ((a : ℝ) * r / q))
        = ∑ s ∈ Finset.range (q / d), e ((a : ℝ) * s / (q / d : ℕ)) := by
      apply Finset.sum_nbij' (fun r => r / d) (fun s => d * s)
      · intro r hr
        simp only [Finset.mem_filter, Finset.mem_range] at hr
        rw [Finset.mem_range]
        exact Nat.div_lt_div_of_lt_of_dvd hdq hr.1
      · intro s hs
        rw [Finset.mem_range] at hs
        simp only [Finset.mem_filter, Finset.mem_range]
        refine ⟨?_, Dvd.intro s rfl⟩
        have h1 : d * s < d * (q / d) := mul_lt_mul_of_pos_left hs hd0
        rwa [hqe] at h1
      · intro r hr
        simp only [Finset.mem_filter] at hr
        exact Nat.mul_div_cancel' hr.2
      · intro s _
        exact Nat.mul_div_cancel_left s hd0
      · intro r hr
        simp only [Finset.mem_filter, Finset.mem_range] at hr
        congr 1
        have hcast : ((q : ℝ)) = (d : ℝ) * ((q / d : ℕ) : ℝ) := by
          exact_mod_cast hqe.symm
        have hrr : (r : ℝ) = (d : ℝ) * ((r / d : ℕ) : ℝ) := by
          exact_mod_cast (Nat.mul_div_cancel' hr.2).symm
        have hd0R : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd0.ne'
        have hm0R : ((q / d : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm0
        rw [hcast, hrr]
        field_simp
    rw [hreindex, char_orthogonality a (q / d) hm0]
  rw [hstep]
  have hcongr : ∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℂ)
      * ∑ r ∈ (Finset.range q).filter (fun r => d ∣ r), e ((a : ℝ) * r / q)
      = ∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℂ)
        * (if ((q / d : ℕ) : ℤ) ∣ a then ((q / d : ℕ) : ℂ) else 0) :=
    Finset.sum_congr rfl (fun d hd => by rw [hinner d hd])
  rw [hcongr, Finset.sum_eq_single q]
  · rw [Nat.div_self hq]
    simp
  · intro d hd hne
    rw [Nat.mem_divisors] at hd
    obtain ⟨hdq, -⟩ := hd
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdq hq
    rw [if_neg, mul_zero]
    intro hdvd
    have hmq : (q / d : ℕ) ∣ q := Nat.div_dvd_of_dvd hdq
    have hgcd : (q / d) ∣ Int.gcd a q := Int.dvd_gcd hdvd (by exact_mod_cast hmq)
    rw [ha] at hgcd
    have hm1 : (q / d : ℕ) = 1 := Nat.dvd_one.mp hgcd
    apply hne
    have hqe : d * (q / d) = q := Nat.mul_div_cancel' hdq
    rw [hm1, mul_one] at hqe
    omega
  · intro hqmem
    exact absurd (Nat.mem_divisors_self q hq') hqmem

/-- **General Ramanujan sum evaluation** (no coprimality hypothesis): the same Möbius
    inclusion–exclusion over character orthogonality that gives `ramanujan_sum_coprime`, but
    stopped *before* the coprime collapse — valid for every `a`. Yields
    `c_q(a) = ∑_{d ∣ q} μ(d)·[ (q/d) ∣ a ]·(q/d)`, the arithmetic engine of the truncated
    singular series `𝔖_P(n) = ∑_{q≤P} μ(q)²c_q(n)/φ(q)²`. -/
lemma ramanujan_sum_divisor (a : ℤ) (q : ℕ) (hq : 0 < q) :
    ∑ r ∈ (Finset.range q).filter (fun r => Nat.gcd r q = 1), e ((a : ℝ) * r / q)
      = ∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℂ)
          * (if ((q / d : ℕ) : ℤ) ∣ a then ((q / d : ℕ) : ℂ) else 0) := by
  classical
  have hq' : q ≠ 0 := hq.ne'
  have hind : ∀ n : ℕ, n ≠ 0 →
      (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℂ)) = if n = 1 then 1 else 0 := by
    intro n hn
    have h : ((ArithmeticFunction.moebius * ArithmeticFunction.zeta :
        ArithmeticFunction ℤ)) n = (1 : ArithmeticFunction ℤ) n := by
      rw [ArithmeticFunction.moebius_mul_coe_zeta]
    rw [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
    by_cases h1 : n = 1
    · rw [if_pos h1, h1]
      simp
    · rw [if_neg h1]
      rw [if_neg h1] at h
      have : ((∑ d ∈ n.divisors, ArithmeticFunction.moebius d : ℤ) : ℂ) = 0 := by
        rw [h]
        norm_num
      push_cast at this
      exact this
  have hdivset : ∀ r : ℕ, (Nat.gcd r q).divisors = q.divisors.filter (fun d => d ∣ r) := by
    intro r
    ext d
    simp only [Nat.mem_divisors, Finset.mem_filter]
    constructor
    · rintro ⟨hdvd, -⟩
      rw [Nat.dvd_gcd_iff] at hdvd
      exact ⟨⟨hdvd.2, hq'⟩, hdvd.1⟩
    · rintro ⟨⟨hdq, -⟩, hdr⟩
      exact ⟨Nat.dvd_gcd hdr hdq, fun hc => hq' (Nat.gcd_eq_zero_iff.mp hc).2⟩
  have hstep : ∑ r ∈ (Finset.range q).filter (fun r => Nat.gcd r q = 1), e ((a : ℝ) * r / q)
      = ∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℂ)
          * ∑ r ∈ (Finset.range q).filter (fun r => d ∣ r), e ((a : ℝ) * r / q) := by
    rw [Finset.sum_filter]
    have hpt : ∀ r ∈ Finset.range q,
        (if Nat.gcd r q = 1 then e ((a : ℝ) * r / q) else 0)
        = ∑ d ∈ q.divisors, if d ∣ r then (ArithmeticFunction.moebius d : ℂ)
            * e ((a : ℝ) * r / q) else 0 := by
      intro r _
      have hgpos : Nat.gcd r q ≠ 0 := fun hc => hq' (Nat.gcd_eq_zero_iff.mp hc).2
      calc (if Nat.gcd r q = 1 then e ((a : ℝ) * r / q) else 0)
          = (if Nat.gcd r q = 1 then (1:ℂ) else 0) * e ((a : ℝ) * r / q) := by
            by_cases h : Nat.gcd r q = 1
            · rw [if_pos h, if_pos h, one_mul]
            · rw [if_neg h, if_neg h, zero_mul]
        _ = (∑ d ∈ (Nat.gcd r q).divisors, (ArithmeticFunction.moebius d : ℂ))
              * e ((a : ℝ) * r / q) := by rw [hind _ hgpos]
        _ = ∑ d ∈ q.divisors.filter (fun d => d ∣ r),
              (ArithmeticFunction.moebius d : ℂ) * e ((a : ℝ) * r / q) := by
            rw [hdivset r, Finset.sum_mul]
        _ = ∑ d ∈ q.divisors, if d ∣ r then (ArithmeticFunction.moebius d : ℂ)
              * e ((a : ℝ) * r / q) else 0 := by
            rw [Finset.sum_filter]
    rw [Finset.sum_congr rfl hpt, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro d _
    rw [Finset.mul_sum, Finset.sum_filter]
  have hinner : ∀ d ∈ q.divisors,
      (∑ r ∈ (Finset.range q).filter (fun r => d ∣ r), e ((a : ℝ) * r / q))
      = if ((q / d : ℕ) : ℤ) ∣ a then ((q / d : ℕ) : ℂ) else 0 := by
    intro d hd
    rw [Nat.mem_divisors] at hd
    obtain ⟨hdq, -⟩ := hd
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdq hq
    have hm0 : q / d ≠ 0 := (Nat.div_pos (Nat.le_of_dvd hq hdq) hd0).ne'
    have hqe : d * (q / d) = q := Nat.mul_div_cancel' hdq
    have hreindex : (∑ r ∈ (Finset.range q).filter (fun r => d ∣ r), e ((a : ℝ) * r / q))
        = ∑ s ∈ Finset.range (q / d), e ((a : ℝ) * s / (q / d : ℕ)) := by
      apply Finset.sum_nbij' (fun r => r / d) (fun s => d * s)
      · intro r hr
        simp only [Finset.mem_filter, Finset.mem_range] at hr
        rw [Finset.mem_range]
        exact Nat.div_lt_div_of_lt_of_dvd hdq hr.1
      · intro s hs
        rw [Finset.mem_range] at hs
        simp only [Finset.mem_filter, Finset.mem_range]
        refine ⟨?_, Dvd.intro s rfl⟩
        have h1 : d * s < d * (q / d) := mul_lt_mul_of_pos_left hs hd0
        rwa [hqe] at h1
      · intro r hr
        simp only [Finset.mem_filter] at hr
        exact Nat.mul_div_cancel' hr.2
      · intro s _
        exact Nat.mul_div_cancel_left s hd0
      · intro r hr
        simp only [Finset.mem_filter, Finset.mem_range] at hr
        congr 1
        have hcast : ((q : ℝ)) = (d : ℝ) * ((q / d : ℕ) : ℝ) := by
          exact_mod_cast hqe.symm
        have hrr : (r : ℝ) = (d : ℝ) * ((r / d : ℕ) : ℝ) := by
          exact_mod_cast (Nat.mul_div_cancel' hr.2).symm
        have hd0R : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd0.ne'
        have hm0R : ((q / d : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm0
        rw [hcast, hrr]
        field_simp
    rw [hreindex, char_orthogonality a (q / d) hm0]
  rw [hstep]
  exact Finset.sum_congr rfl (fun d hd => by rw [hinner d hd])


/-- **The Dirichlet-kernel square's Fourier coefficient is the pair count**:
    `∫₀¹ D_N(α)² e(−nα) dα = #{(i,j) : i,j < N, i+j = n}` — the model's contribution to
    each representation count, in exact form. -/
lemma model_sq_coeff (N n : ℕ) :
    ∫ α in (0:ℝ)..1,
        (∑ m ∈ Finset.range N, e ((m : ℝ) * α)) ^ 2 * e (-((n : ℝ) * α))
      = (((Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 = n)).card : ℂ) := by
  have h := fourier_coeff_sq (fun _ => (1 : ℂ)) N n
  simp only [one_mul] at h
  rw [h]
  rw [Finset.sum_const, nsmul_eq_mul, mul_one]

/-- **The tent count**: for `n < N` the number of ordered pairs `i+j = n` inside the
    `N×N` box is exactly `n+1` — the model main term grows linearly on the upper block,
    which is what the reduction's `δ`-lower-bound consumes. -/
lemma pair_count_eq (N n : ℕ) (hn : n < N) :
    ((Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 = n)).card = n + 1 := by
  have himg : (Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 = n)
      = (Finset.range (n + 1)).image (fun i => (i, n - i)) := by
    ext p
    obtain ⟨p1, p2⟩ := p
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_image,
      Prod.mk.injEq]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨p1, by omega, rfl, by omega⟩
    · rintro ⟨i, hi, rfl, rfl⟩
      omega
  rw [himg, Finset.card_image_of_injOn, Finset.card_range]
  intro i _ j _ h
  exact (Prod.mk.injEq _ _ _ _).mp h |>.1

/-- Upper slope of the tent: for `N ≤ n ≤ 2N−2` the pair count is `2N−1−n`. -/
lemma pair_count_eq_upper (N n : ℕ) (hn1 : N ≤ n) (hn2 : n ≤ 2 * N - 2) :
    ((Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 = n)).card
      = 2 * N - 1 - n := by
  rcases Nat.eq_zero_or_pos N with rfl | hN0
  · simp
  have hN : 2 ≤ N := by omega
  have himg : (Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 = n)
      = (Finset.Icc (n - N + 1) (N - 1)).image (fun i => (i, n - i)) := by
    ext p
    obtain ⟨p1, p2⟩ := p
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_image,
      Finset.mem_Icc, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨p1, ⟨by omega, by omega⟩, rfl, by omega⟩
    · rintro ⟨i, ⟨hi1, hi2⟩, rfl, rfl⟩
      omega
  rw [himg, Finset.card_image_of_injOn, Nat.card_Icc]
  · omega
  · intro i _ j _ h
    exact (Prod.mk.injEq _ _ _ _).mp h |>.1

/-- Beyond the tent: for `n ≥ 2N−1` the pair count vanishes. -/
lemma pair_count_eq_zero (N n : ℕ) (hn : 2 * N - 1 ≤ n) (hN : 0 < N) :
    ((Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 = n)).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro ⟨p1, p2⟩ hp
  rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
  simp only
  omega

open MeasureTheory in
/-- **Small-set L² bound**: on a measurable `s ⊆ (0,1]` where `‖f‖ ≤ B`, the L² mass is
    at most `vol(s)·B²` — the per-window error estimate: window measure `2/(q(Q+1))`
    times the squared window evaluation. -/
lemma setIntegral_sq_le_measure_mul_sup (f : ℝ → ℂ) (hf : Continuous f) (s : Set ℝ)
    (hs : MeasurableSet s) (hsub : s ⊆ Set.Ioc (0:ℝ) 1) (B : ℝ)
    (hB : ∀ x ∈ s, ‖f x‖ ≤ B) :
    ∫ x in s, ‖f x‖ ^ 2 ≤ (volume s).toReal * B ^ 2 := by
  have hint : IntegrableOn (fun x => ‖f x‖ ^ 2) s volume :=
    ((hf.norm.pow 2).integrableOn_Ioc).mono_set hsub
  have hfin : volume s ≠ ⊤ := by
    apply ne_top_of_le_ne_top _ (measure_mono hsub)
    simp [Real.volume_Ioc]
  calc ∫ x in s, ‖f x‖ ^ 2
      ≤ ∫ _x in s, B ^ 2 := by
        apply setIntegral_mono_on hint (integrableOn_const hfin) hs
        intro x hx
        have h := hB x hx
        have h0 : 0 ≤ ‖f x‖ := norm_nonneg _
        nlinarith
    _ = (volume s).toReal * B ^ 2 := by
        rw [setIntegral_const, smul_eq_mul]
        rfl

/-- A Farey window's measure in usable form: `vol(B̄(c,r)) = 2r`. -/
lemma window_volume (c r : ℝ) (hr : 0 ≤ r) :
    (MeasureTheory.volume (Metric.closedBall c r)).toReal = 2 * r := by
  rw [Real.volume_closedBall, ENNReal.toReal_ofReal (by linarith)]

/-- Trivial bound for Ramanujan-type sums: `‖∑_{units} e(ar/q)‖ ≤ φ(q)`. -/
lemma ramanujan_sum_norm_le (a : ℤ) (q : ℕ) :
    ‖∑ r ∈ (Finset.range q).filter (fun r => Nat.gcd r q = 1), e ((a : ℝ) * r / q)‖
      ≤ (Nat.totient q : ℝ) := by
  calc ‖∑ r ∈ (Finset.range q).filter (fun r => Nat.gcd r q = 1), e ((a : ℝ) * r / q)‖
      ≤ ∑ r ∈ (Finset.range q).filter (fun r => Nat.gcd r q = 1), ‖e ((a : ℝ) * r / q)‖ :=
        norm_sum_le _ _
    _ = ((Finset.range q).filter (fun r => Nat.gcd r q = 1)).card := by
        simp [e_norm]
    _ = (Nat.totient q : ℝ) := by
        rw [Nat.totient]
        congr 2
        ext r
        simp [Nat.Coprime, Nat.gcd_comm]

open MeasureTheory in
/-- Two-set L¹ subadditivity for nonneg integrands on subsets of `(0,1]`. -/
lemma setIntegral_union_le (A B : Set ℝ) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAsub : A ⊆ Set.Ioc (0:ℝ) 1) (hBsub : B ⊆ Set.Ioc (0:ℝ) 1)
    (g : ℝ → ℝ) (hg : Continuous g) (hgnn : ∀ x, 0 ≤ g x) :
    ∫ x in A ∪ B, g x ≤ (∫ x in A, g x) + ∫ x in B, g x := by
  have hint : IntegrableOn g (Set.Ioc (0:ℝ) 1) volume := hg.integrableOn_Ioc
  have hunion : A ∪ (B \ A) = A ∪ B := Set.union_diff_self
  calc ∫ x in A ∪ B, g x
      = ∫ x in A ∪ (B \ A), g x := by rw [hunion]
    _ = (∫ x in A, g x) + ∫ x in B \ A, g x := by
        apply setIntegral_union Set.disjoint_sdiff_right (hB.diff hA)
        · exact hint.mono_set hAsub
        · exact hint.mono_set (le_trans Set.diff_subset hBsub)
    _ ≤ (∫ x in A, g x) + ∫ x in B, g x := by
        have hmono : ∫ x in B \ A, g x ≤ ∫ x in B, g x := by
          apply setIntegral_mono_set (hint.mono_set hBsub)
          · filter_upwards with x using hgnn x
          · exact HasSubset.Subset.eventuallyLE Set.diff_subset
        linarith

open MeasureTheory in
/-- **Finite-union L¹ subadditivity**: the integral of a nonneg integrand over a finite
    union is at most the sum of the per-set integrals — the major-arc integral's split
    over the anchor windows (disjointness not even needed for the ≤ direction). -/
lemma setIntegral_biUnion_le_sum {ι : Type*} [DecidableEq ι] (s : Finset ι) (t : ι → Set ℝ)
    (ht : ∀ i ∈ s, MeasurableSet (t i)) (hsub : ∀ i ∈ s, t i ⊆ Set.Ioc (0:ℝ) 1)
    (g : ℝ → ℝ) (hg : Continuous g) (hgnn : ∀ x, 0 ≤ g x) :
    ∫ x in ⋃ i ∈ s, t i, g x ≤ ∑ i ∈ s, ∫ x in t i, g x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have hun : (⋃ i ∈ insert a s, t i) = t a ∪ ⋃ i ∈ s, t i := by
      simp [Set.biUnion_insert]
    rw [hun]
    have htm : ∀ i ∈ s, MeasurableSet (t i) := fun i hi => ht i (Finset.mem_insert_of_mem hi)
    have hsm : ∀ i ∈ s, t i ⊆ Set.Ioc (0:ℝ) 1 := fun i hi => hsub i (Finset.mem_insert_of_mem hi)
    have hUm : MeasurableSet (⋃ i ∈ s, t i) := by
      apply MeasurableSet.biUnion (Finset.countable_toSet s)
      intro i hi
      exact htm i hi
    have hUsub : (⋃ i ∈ s, t i) ⊆ Set.Ioc (0:ℝ) 1 := by
      apply Set.iUnion₂_subset
      intro i hi
      exact hsm i hi
    calc ∫ x in t a ∪ ⋃ i ∈ s, t i, g x
        ≤ (∫ x in t a, g x) + ∫ x in ⋃ i ∈ s, t i, g x :=
          setIntegral_union_le _ _ (ht a (Finset.mem_insert_self a s)) hUm
            (hsub a (Finset.mem_insert_self a s)) hUsub g hg hgnn
      _ ≤ (∫ x in t a, g x) + ∑ i ∈ s, ∫ x in t i, g x := by
          gcongr
          exact ih htm hsm

end MinorArc
end Principia.Common.Goldbach
