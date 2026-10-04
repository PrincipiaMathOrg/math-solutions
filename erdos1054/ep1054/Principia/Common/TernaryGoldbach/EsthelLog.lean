/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.EsthelEta2K
import Principia.Common.TernaryGoldbach.Bostb1Spine
import Principia.Common.TernaryGoldbach.Bostb1Main

set_option autoImplicit false

/-!
# `MPB1.EsthelLogEta2` PROVED -- `eq:esthel2` of `lem:bostb1`, the `eq:kuche2` branch

`lem:bostb1` (book `typeI.tex` 1153-1478) is `lem:bosta2` with the per-`m` estimate multiplied
by `log(x/m)` (`MPB1.TromLB`). The proof of `eq:esthel2` in the `eq:kuche2` branch (1399-1466)
uses the same cover as `eq:esthel` (`MPE2.esthel_keks`): for `D' = min(c₂x/q, D)` and
`R = max(c₂x/q, q/2)`,

* `piece1L` -- `eq:bobo`: `m ≤ q/2` (and `m ≤ D`), `lem:thina` with `B, C` multiplied by `log x`
  (the factor cancels inside the `log`);
* `piece2L` -- `eq:bocio`: `q/2 < m ≤ D'`, `q ∤ m`, `lem:couscous` on each window with the weight
  `log(x/(j + 1/2)q)`, then `sumS`:
  `∑_{j<J} (j + 3/2) log(x/(j + 1/2)q) ≤ log(2x/q) + (2D'/q + D'²/2q²) log(√e x/D')`;
* `piece3L` -- `eq:caron` + `eq:binbed`: `R < m ≤ D`, `lem:gotog` on each window with the weight
  `log(x/(jq + R))`; the `√(1 + q/(jq+R))` part telescopes against `G(t) = t log(ex/t)`.

Each "integral" of the book is replaced by a telescoping antiderivative: `g_step`
(`(b - a)log(x/b) ≤ G(b) - G(a)`, from `log y ≤ y - 1`) and `h_step`
(`(b - a)·a log(x/a) ≤ H(b) - H(a)`, `H(t) = (t²/2)log(√e x/t)`, by the mean value theorem, as
`t log(x/t)` increases on `(0, x/e]`).

**One correction to the printed argument, no change to the statement.** In `eq:bocio` the book
bounds `(q³/x)log(2x/q)` and `(2D'q²/x)log(√e x/D')` each by `4√(2c₂x)·(...)` and then adds the
two logarithms into `log(2√e x/c₂)`; that addition needs `qD' ≥ c₂x`, the opposite of
`D' ≤ c₂x/q`. The stated bound is nevertheless TRUE: `(q³/x) ≤ 2c₂q`, and
`D' log(√e x/D') ≤ (c₂x/q)log(√e q/c₂)` because `t log(√e x/t)` increases up to `x/√e ≥ c₂x/q`
(`q ≥ 2`; for `q = 1` the sum is empty), so the two terms are at most
`2c₂q·log(2√e x/c₂) ≤ 2c₂√(2c₂x)·log(2√e x/c₂)` -- which is `eq:kuche2`'s last term exactly.
-/

namespace Principia.Common.TernaryGoldbach.MPEL

open Real Finset Principia.Common.TrigSumN
open Principia.Common.TernaryGoldbach.MPc Principia.Common.TernaryGoldbach.MPB2
  Principia.Common.TernaryGoldbach.MPE2 Principia.Common.TernaryGoldbach.MPB1

/-! ## (1) The per-`m` estimate written at `α = 2β` -/

/-- `T` obeys the per-`m` estimate of `lem:bostb1` written with `α = 2β`, for `d ≤ x/4`. -/
def TBL (x α : ℝ) (t : ℕ → ℝ) : Prop :=
  ∀ d : ℕ, 1 ≤ d → (d : ℝ) ≤ x / 4 → 0 ≤ t d ∧
    t d ≤ log (x / d) * (x / (2 * d) + eta1 / 2) ∧
    t d * |sin (π * (α * d))| ≤ log (x / d) * (eta1 / 2) ∧
    t d * sin (π * (α * d)) ^ 2 ≤ log (x / d) * (d / x * (c0 / 2))

theorem tbl_of_tromLB (x β : ℝ) (T : ℕ → ℝ) (h : TromLB x β T) : TBL x (2 * β) T := by
  intro d hd hdx
  obtain ⟨h0, h1, h2, h3⟩ := h d hd hdx
  have e : π * (2 * β * d) = 2 * π * d * β := by ring
  rw [e]
  exact ⟨h0, h1, h2, h3⟩

/-! ## (2) Constants and logarithms -/

/-- `c₂ < 0.7` (`√31.521 ≥ 5.6`, `π < 3.15`). -/
theorem c2_lt : c2 < 0.7 := by
  have hc0 := c0_pos
  have hs : (5.6 : ℝ) ≤ √c0 := by
    have := Real.sqrt_le_sqrt (show (5.6 : ℝ) ^ 2 ≤ c0 by unfold c0; norm_num)
    rwa [Real.sqrt_sq (by norm_num)] at this
  have hpi := Real.pi_lt_d2
  unfold c2
  rw [div_lt_iff₀ (by positivity)]
  linarith

/-- `log(2√e·x/c₂) = 1/2 + log(2x) - log c₂`. -/
theorem log_2sqe (x : ℝ) (hx : 0 < x) :
    log (2 * √(exp 1) * x / c2) = 1 / 2 + (log (2 * x) - log c2) := by
  have hc2 := c2_pos
  have e : 2 * √(exp 1) * x / c2 = √(exp 1) * ((2 * x) / c2) := by ring
  rw [e, Real.log_mul (by positivity) (by positivity), Real.log_div (by positivity) hc2.ne',
    Real.log_sqrt (Real.exp_pos 1).le, Real.log_exp]

/-- `log(x/d) ≤ log x - log u` for `0 < u ≤ d`. -/
theorem log_div_le (x d u : ℝ) (hx : 0 < x) (hu : 0 < u) (hud : u ≤ d) :
    log (x / d) ≤ log x - log u := by
  have hd : 0 < d := lt_of_lt_of_le hu hud
  rw [Real.log_div hx.ne' hd.ne']
  have := Real.log_le_log hu hud
  linarith

theorem log_div_nonneg (x d : ℝ) (hd : 0 < d) (hdx : d ≤ x) : 0 ≤ log (x / d) :=
  Real.log_nonneg (by rw [le_div_iff₀ hd]; linarith)

/-! ## (3) Antiderivatives in place of the book's integrals -/

/-- `G(t) = t(1 + log x - log t)` (`= t log(ex/t)`). -/
noncomputable def gG (x t : ℝ) : ℝ := t * ((1 + log x) - log t)

/-- `φ(t) = t(log x - log t)` (`= t log(x/t)`). -/
noncomputable def phiL (x t : ℝ) : ℝ := t * (log x - log t)

/-- `H(t) = (t²/2)(1/2 + log x - log t)` (`= (t²/2)log(√e x/t)`, `H' = φ`). -/
noncomputable def hH (x t : ℝ) : ℝ := t ^ 2 / 2 * ((1 / 2 + log x) - log t)

/-- `ψ(t) = t(1/2 + log x - log t)` (`= t log(√e x/t)`). -/
noncomputable def psiL (x t : ℝ) : ℝ := t * ((1 / 2 + log x) - log t)

/-- **`G` telescopes the decreasing `log(x/t)`**: `(b - a)log(x/b) ≤ G(b) - G(a)`, `0 < a ≤ b`. -/
theorem g_step (x a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    (b - a) * (log x - log b) ≤ gG x b - gG x a := by
  unfold gG
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have h2 := Real.log_le_sub_one_of_pos (show 0 < b / a by positivity)
  rw [Real.log_div hb.ne' ha.ne'] at h2
  have h3 : a * (log b - log a) ≤ b - a := by
    have := mul_le_mul_of_nonneg_left h2 ha.le
    have e : a * (b / a - 1) = b - a := by field_simp
    linarith
  nlinarith

/-- The mean value bound: `Φ' = φ ≥ C` on `[a, b]` gives `C(b - a) ≤ Φ(b) - Φ(a)`. -/
theorem mvt_lower (Φ φ : ℝ → ℝ) (a b C : ℝ) (hab : a ≤ b)
    (hd : ∀ t ∈ Set.Icc a b, HasDerivAt Φ (φ t) t) (hC : ∀ t ∈ Set.Icc a b, C ≤ φ t) :
    C * (b - a) ≤ Φ b - Φ a := by
  refine (convex_Icc a b).mul_sub_le_image_sub_of_le_deriv
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt)
    (fun t ht => ?_) a (Set.left_mem_Icc.mpr hab) b (Set.right_mem_Icc.mpr hab) hab
  rw [(hd t (interior_subset ht)).deriv]
  exact hC t (interior_subset ht)

theorem hasDerivAt_phiL (x t : ℝ) (ht : 0 < t) :
    HasDerivAt (phiL x) (log x - log t - 1) t := by
  have := (hasDerivAt_id' t).mul ((hasDerivAt_const t (log x)).sub (Real.hasDerivAt_log ht.ne'))
  refine this.congr_deriv ?_
  simp only [Pi.sub_apply]
  field_simp
  ring

theorem hasDerivAt_psiL (x t : ℝ) (ht : 0 < t) :
    HasDerivAt (psiL x) (log x - log t - 1 / 2) t := by
  have := (hasDerivAt_id' t).mul
    ((hasDerivAt_const t (1 / 2 + log x)).sub (Real.hasDerivAt_log ht.ne'))
  refine this.congr_deriv ?_
  simp only [Pi.sub_apply]
  field_simp
  ring

theorem hasDerivAt_hH (x t : ℝ) (ht : 0 < t) : HasDerivAt (hH x) (phiL x t) t := by
  have := (((hasDerivAt_id' t).pow 2).div_const 2).mul
    ((hasDerivAt_const t (1 / 2 + log x)).sub (Real.hasDerivAt_log ht.ne'))
  refine this.congr_deriv ?_
  unfold phiL
  simp only [Pi.sub_apply, Pi.pow_apply]
  field_simp
  ring

/-- `φ` increases on `(0, x/e]`. -/
theorem phiL_mono (x a b : ℝ) (hx : 0 < x) (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ x / exp 1) :
    phiL x a ≤ phiL x b := by
  have hC : ∀ t ∈ Set.Icc a b, (0 : ℝ) ≤ log x - log t - 1 := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le ha ht.1
    have h1 : log t ≤ log (x / exp 1) := Real.log_le_log ht0 (ht.2.trans hb)
    rw [Real.log_div hx.ne' (Real.exp_pos 1).ne', Real.log_exp] at h1
    linarith
  have := mvt_lower (phiL x) (fun t => log x - log t - 1) a b 0 hab
    (fun t ht => hasDerivAt_phiL x t (lt_of_lt_of_le ha ht.1)) hC
  linarith

/-- `ψ` increases on `(0, x/√e]`. -/
theorem psiL_mono (x a b : ℝ) (hx : 0 < x) (ha : 0 < a) (hab : a ≤ b)
    (hb : b ≤ x / exp (1 / 2)) : psiL x a ≤ psiL x b := by
  have hC : ∀ t ∈ Set.Icc a b, (0 : ℝ) ≤ log x - log t - 1 / 2 := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le ha ht.1
    have h1 : log t ≤ log (x / exp (1 / 2)) := Real.log_le_log ht0 (ht.2.trans hb)
    rw [Real.log_div hx.ne' (Real.exp_pos _).ne', Real.log_exp] at h1
    linarith
  have := mvt_lower (psiL x) (fun t => log x - log t - 1 / 2) a b 0 hab
    (fun t ht => hasDerivAt_psiL x t (lt_of_lt_of_le ha ht.1)) hC
  linarith

/-- **`H` telescopes the increasing `t log(x/t)`**: `(b - a)φ(a) ≤ H(b) - H(a)` on `(0, x/e]`. -/
theorem h_step (x a b : ℝ) (hx : 0 < x) (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ x / exp 1) :
    phiL x a * (b - a) ≤ hH x b - hH x a :=
  mvt_lower (hH x) (phiL x) a b (phiL x a) hab
    (fun t ht => hasDerivAt_hH x t (lt_of_lt_of_le ha ht.1))
    (fun t ht => phiL_mono x a t hx ha ht.1 (ht.2.trans hb))

/-- **The weighted window sum of `eq:bocio`**: for `J ≥ 1` and `(J - 1/2)q ≤ D ≤ x/e`,
`∑_{j<J} (j + 3/2) log(x/(j + 1/2)q) ≤ log(2x/q) + (2D/q + D²/2q²) log(√e x/D)`. -/
theorem sumS (x q D : ℝ) (J : ℕ) (hx : 0 < x) (hq : 0 < q) (hJ : 1 ≤ J)
    (hJD : ((J : ℝ) - 1 / 2) * q ≤ D) (hDx : D ≤ x / exp 1) :
    ∑ j ∈ range J, ((j : ℝ) + 3 / 2) * (log x - log (((j : ℝ) + 1 / 2) * q)) ≤
      (log x - log (q / 2)) + (2 * D / q + D ^ 2 / (2 * q ^ 2)) * (1 / 2 + (log x - log D)) := by
  have he : x / exp 1 ≤ x :=
    div_le_self hx.le (by have := Real.add_one_le_exp (1 : ℝ); linarith)
  obtain ⟨K, rfl⟩ : ∃ K, J = K + 1 := ⟨J - 1, by omega⟩
  set u : ℕ → ℝ := fun j => ((j : ℝ) + 1 / 2) * q with hu
  have hu0 : ∀ j, 0 < u j := fun j => by simp only [hu]; positivity
  have hus : ∀ j, u (j + 1) - u j = q := fun j => by simp only [hu]; push_cast; ring
  have huK : u K ≤ D := by
    simp only [hu]
    push_cast at hJD
    linarith
  have hum : ∀ j, j ≤ K → u j ≤ u K := fun j hj => by
    simp only [hu]
    have : (j : ℝ) ≤ K := by exact_mod_cast hj
    nlinarith
  have hD0 : 0 < D := lt_of_lt_of_le (hu0 K) huK
  have hlu : ∀ j, j ≤ K → log (u j) ≤ log x := fun j hj =>
    Real.log_le_log (hu0 j) ((hum j hj).trans (huK.trans (hDx.trans he)))
  have esplit : ∑ j ∈ range (K + 1), ((j : ℝ) + 3 / 2) * (log x - log (((j : ℝ) + 1 / 2) * q)) =
      ∑ j ∈ range (K + 1), (log x - log (u j)) + 1 / q * ∑ j ∈ range (K + 1), phiL x (u j) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hu, phiL]
    field_simp
    ring
  -- the `log` part, telescoped against `G`
  have hA : ∑ j ∈ range (K + 1), (log x - log (u j)) ≤ (log x - log (q / 2)) + gG x D / q := by
    rw [Finset.sum_range_succ']
    have hstep : ∀ j ∈ range K,
        log x - log (u (j + 1)) ≤ (gG x (u (j + 1)) - gG x (u j)) / q := by
      intro j _
      have := g_step x (u j) (u (j + 1)) (hu0 j) (by linarith [hus j])
      rw [hus j] at this
      rw [le_div_iff₀ hq]
      linarith
    have h1 := Finset.sum_le_sum hstep
    rw [← Finset.sum_div, Finset.sum_range_sub (fun j => gG x (u j))] at h1
    have hK := g_step x (u K) D (hu0 K) huK
    have hDl : 0 ≤ log x - log D := by
      have := Real.log_le_log hD0 (hDx.trans he)
      linarith
    have hg0 : 0 ≤ gG x (u 0) := by
      unfold gG
      have := hlu 0 (Nat.zero_le _)
      have := hu0 0
      nlinarith
    have h2 : (gG x (u K) - gG x (u 0)) / q ≤ gG x D / q :=
      div_le_div_of_nonneg_right (by nlinarith [mul_nonneg (sub_nonneg.mpr huK) hDl]) hq.le
    have hu00 : log x - log (u 0) = log x - log (q / 2) := by
      simp only [hu]
      push_cast
      ring_nf
    linarith
  -- the `t log(x/t)` part, telescoped against `H`
  have hB : ∑ j ∈ range (K + 1), phiL x (u j) ≤ hH x D / q + phiL x D := by
    rw [Finset.sum_range_succ]
    have hstep : ∀ j ∈ range K, phiL x (u j) ≤ (hH x (u (j + 1)) - hH x (u j)) / q := by
      intro j hj
      have hjK : j + 1 ≤ K := Finset.mem_range.mp hj
      have := h_step x (u j) (u (j + 1)) hx (hu0 j) (by linarith [hus j])
        ((hum (j + 1) hjK).trans (huK.trans hDx))
      rw [hus j] at this
      rw [le_div_iff₀ hq]
      linarith
    have h1 := Finset.sum_le_sum hstep
    rw [← Finset.sum_div, Finset.sum_range_sub (fun j => hH x (u j))] at h1
    have hK := h_step x (u K) D hx (hu0 K) huK hDx
    have hphiK0 : 0 ≤ phiL x (u K) := by
      unfold phiL
      have := hlu K le_rfl
      have := hu0 K
      nlinarith
    have hH0 : 0 ≤ hH x (u 0) := by
      unfold hH
      have := hlu 0 (Nat.zero_le _)
      have : 0 ≤ (u 0) ^ 2 / 2 := by positivity
      nlinarith
    have hphi := phiL_mono x (u K) D hx (hu0 K) huK hDx
    have h2 : (hH x (u K) - hH x (u 0)) / q ≤ hH x D / q :=
      div_le_div_of_nonneg_right (by nlinarith [mul_nonneg hphiK0 (sub_nonneg.mpr huK)]) hq.le
    linarith
  rw [esplit]
  have hfin : gG x D / q + 1 / q * (hH x D / q + phiL x D) =
      (2 * D / q + D ^ 2 / (2 * q ^ 2)) * (1 / 2 + (log x - log D)) := by
    unfold gG hH phiL
    field_simp
    ring
  have := mul_le_mul_of_nonneg_left hB (by positivity : (0 : ℝ) ≤ 1 / q)
  linarith

/-! ## (4) Piece 1 -- `eq:bobo`, `m ≤ q/2` (`lem:thina`) -/

/-- **`eq:bobo`**: `∑_{m ≤ min(q/2, D)} T ≤ (2|η₂'|₁/π) q max(1, log(c₀e³q²/(4π|η₂'|₁x))) log x`. -/
theorem piece1L (x α β Q D : ℝ) (a : ℤ) (q : ℕ) (hq : 1 ≤ q) (hcop : Int.gcd a q = 1)
    (hα : α = a / q + β / (q * Q)) (hβ : |β| ≤ 1) (hqQ : (q : ℝ) ≤ Q) (hx : 1 < x)
    (hD0 : 0 ≤ D) (hDx : D ≤ x / 4) (t : ℕ → ℝ) (ht : TBL x α t) :
    ∑ d ∈ Ioc 0 (min (q / 2) ⌊D⌋₊), t d ≤
      2 * eta1 / π * q *
        max 1 (log (c0 * exp 3 * (q : ℝ) ^ 2 / (4 * π * eta1 * x))) * log x := by
  have hx0 : 0 < x := by linarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hLx : 0 < log x := Real.log_pos hx
  have he := eta1_pos
  have hc0 := c0_pos
  set n2 := min (q / 2) ⌊D⌋₊ with hn2_def
  have hfil : (Ioc 0 n2).filter (fun n => ¬ q ∣ n) = Ioc 0 n2 := by
    refine Finset.filter_true_of_mem fun n hn => ?_
    have h1 := Finset.mem_Ioc.mp hn
    have : n ≤ q / 2 := le_trans h1.2 (min_le_left _ _)
    exact Nat.not_dvd_of_pos_of_lt h1.1 (by omega)
  have hh : ((q / 2 : ℕ) : ℝ) ≤ q / 2 := by
    rw [le_div_iff₀ (by norm_num)]
    have : q / 2 * 2 ≤ q := Nat.div_mul_le_self q 2
    exact_mod_cast this
  have hn2q : (n2 : ℝ) ≤ q / 2 := le_trans (by exact_mod_cast min_le_left _ _) hh
  have hel : ∀ n ∈ (Ioc 0 n2).filter (fun n => ¬ q ∣ n),
      1 ≤ n ∧ (n : ℝ) ≤ q / 2 ∧ (n : ℝ) ≤ x / 4 := by
    intro n hn
    have hn' := Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1
    refine ⟨hn'.1, le_trans (by exact_mod_cast hn'.2) hn2q, ?_⟩
    have h1 : n ≤ ⌊D⌋₊ := le_trans hn'.2 (min_le_right _ _)
    have h2 : (n : ℝ) ≤ ⌊D⌋₊ := by exact_mod_cast h1
    linarith [Nat.floor_le hD0]
  have hlog : ∀ n : ℕ, 1 ≤ n → log (x / n) ≤ log x := by
    intro n hn
    have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have := log_div_le x n 1 hx0 one_pos h1
    rwa [Real.log_one, sub_zero] at this
  have hB : (0 : ℝ) ≤ log x * (eta1 / 2) := by positivity
  have hC : (0 : ℝ) ≤ log x * (c0 * q / (4 * x)) := by positivity
  have key := thinaN α β Q (log x * (eta1 / 2)) (log x * (c0 * q / (4 * x))) a q hq hcop hα hβ
    hB hC 0 n2 (by omega) (by linarith) t
    (fun n hn => by
      obtain ⟨h1, -, h3⟩ := hel n hn
      refine (ht n h1 h3).2.2.1.trans ?_
      exact mul_le_mul_of_nonneg_right (hlog n h1) (by positivity))
    (fun n hn => by
      obtain ⟨h1, h2, h3⟩ := hel n hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast h1
      have hlg := log_div_nonneg x n hn0 (by linarith)
      refine (ht n h1 h3).2.2.2.trans ?_
      refine mul_le_mul (hlog n h1) ?_ (by positivity) hLx.le
      rw [div_mul_eq_mul_div, div_le_div_iff₀ hx0 (by positivity)]
      nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr h2) hc0.le) hx0.le])
  rw [hfil] at key
  have hlog2 : log (log x * (c0 * q / (4 * x)) * exp 3 * q / (log x * (eta1 / 2) * π)) =
      log 2 + log (c0 * exp 3 * (q : ℝ) ^ 2 / (4 * π * eta1 * x)) := by
    rw [← Real.log_mul (by norm_num) (by positivity)]
    congr 1
    field_simp
  rw [hlog2] at key
  have hm := max_two_le (log (c0 * exp 3 * (q : ℝ) ^ 2 / (4 * π * eta1 * x)))
  have hk : 0 ≤ eta1 * q / π * log x := by positivity
  have hk2 := mul_le_mul_of_nonneg_left hm hk
  calc _ ≤ _ := key
    _ = eta1 * q / π * log x *
          max 2 (log 2 + log (c0 * exp 3 * (q : ℝ) ^ 2 / (4 * π * eta1 * x))) := by ring
    _ ≤ _ := hk2
    _ = _ := by ring

/-! ## (5) Piece 2 -- `eq:bocio`, `q/2 < m ≤ D'`, `q ∤ m` (`lem:couscous`) -/

/-- `c₂^{3/2}√(2x) = c₂√(2c₂x)`. -/
theorem rpow_c2 (x : ℝ) : c2 ^ ((3 : ℝ) / 2) * √(2 * x) = c2 * √(2 * c2 * x) := by
  have hc2 := c2_pos
  rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hc2, Real.rpow_one,
    ← Real.sqrt_eq_rpow, show 2 * c2 * x = c2 * (2 * x) by ring, Real.sqrt_mul hc2.le]
  ring

/-- **One weighted `lem:couscous` window of `eq:bocio`**: window `j` (`(h + jq, h + jq + q]`,
truncated at `N`, `q ∤ m`) with the weight `log(x/(j + 1/2)q)`. -/
theorem cwinL (x α β Q : ℝ) (a : ℤ) (q : ℕ) (hq : 1 ≤ q) (hcop : Int.gcd a q = 1)
    (hα : α = a / q + β / (q * Q)) (hβ : |β| ≤ 1) (hx0 : 0 < x) (t : ℕ → ℝ) (ht : TBL x α t)
    (h j N : ℕ) (hhr : (h : ℝ) ≤ q / 2) (hhr2 : ((q : ℝ) - 1) / 2 ≤ h)
    (hjq : h + j * q + 1 ≤ N) (hNx : (N : ℝ) ≤ x / 4) (hNQ : (N : ℝ) ≤ Q / 2) :
    ∑ d ∈ Ioc (h + j * q) (h + j * q + q), (if d ≤ N ∧ ¬ q ∣ d then t d else 0) ≤
      20 / (3 * π ^ 2) * ((log x - log (((j : ℝ) + 1 / 2) * q)) *
        (c0 * ((j : ℝ) + 3 / 2) * q / (2 * x))) * q ^ 2 := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hc0 := c0_pos
  have hu0 : (0 : ℝ) < ((j : ℝ) + 1 / 2) * q := by positivity
  have hjqr : ((h + j * q + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast hjq
  push_cast at hjqr
  have hLj : 0 ≤ log x - log (((j : ℝ) + 1 / 2) * q) := by
    have h1 : ((j : ℝ) + 1 / 2) * q ≤ x := by linarith
    have := Real.log_le_log hu0 h1
    linarith
  rw [window_trunc]
  refine couscousN α β Q _ a q hq hcop hα hβ (by positivity) (h + j * q)
    (min (h + j * q + q) N) (by omega) ?_ t ?_
  · have : ((min (h + j * q + q) N : ℕ) : ℝ) ≤ N := by exact_mod_cast min_le_right _ _
    linarith
  · intro d hd
    have hd' := Finset.mem_Ioc.mp (Finset.mem_filter.mp hd).1
    have hd1 : 1 ≤ d := by omega
    have hdle : d ≤ h + j * q + q := le_trans hd'.2 (min_le_left _ _)
    have hdN : d ≤ N := le_trans hd'.2 (min_le_right _ _)
    have hdr : (d : ℝ) ≤ ((j : ℝ) + 3 / 2) * q := by
      have h1 : ((d : ℕ) : ℝ) ≤ ((h + j * q + q : ℕ) : ℝ) := by exact_mod_cast hdle
      push_cast at h1
      linarith
    have hdl : ((j : ℝ) + 1 / 2) * q ≤ d := by
      have h1 : h + j * q + 1 ≤ d := hd'.1
      have h2 : ((h + j * q + 1 : ℕ) : ℝ) ≤ d := by exact_mod_cast h1
      push_cast at h2
      linarith
    have hdx : (d : ℝ) ≤ x / 4 := by
      have : (d : ℝ) ≤ N := by exact_mod_cast hdN
      linarith
    refine (ht d hd1 hdx).2.2.2.trans ?_
    refine mul_le_mul (log_div_le x d _ hx0 hu0 hdl) ?_ (by positivity) hLj
    rw [div_mul_eq_mul_div, div_le_div_iff₀ hx0 (by positivity)]
    have := mul_le_mul_of_nonneg_left hdr (by positivity : (0 : ℝ) ≤ c0 * x)
    linarith

/-- **The arithmetic closing `eq:bocio`** (the corrected combination of the module doc). -/
theorem p2_arith (x q D' S : ℝ) (hx0 : 0 < x) (hq2 : 2 ≤ q) (hD0 : 0 < D')
    (hDq : D' * q ≤ c2 * x) (hqq : q ^ 2 ≤ 2 * c2 * x) (hqx : q ≤ 2 * x) (hDx : D' ≤ x)
    (hS : S ≤ (log (2 * x) - log q) + (2 * D' / q + D' ^ 2 / (2 * q ^ 2)) *
      (1 / 2 + (log x - log D'))) :
    10 * c0 / (3 * π ^ 2) * (q ^ 3 / x) * S ≤
      2 * √c0 / π * (D' * (1 / 2 + (log x - log D'))) +
        20 * c0 * c2 ^ ((3 : ℝ) / 2) / (3 * π ^ 2) * √(2 * x) *
          log (2 * √(exp 1) * x / c2) := by
  have hq0 : 0 < q := by linarith
  have hc0 := c0_pos
  have hc2 := c2_pos
  have hc2l := c2_lt
  have hpi := Real.pi_pos
  have hl5 := log_2sqe x hx0
  have hlc2 : log c2 < 0 := Real.log_neg hc2 (by linarith)
  have hlD : log D' ≤ log x := Real.log_le_log hD0 hDx
  have hl2x : 0 ≤ log (2 * x) := Real.log_nonneg (by linarith)
  have hM0 : 0 ≤ 1 / 2 + (log (2 * x) - log c2) := by linarith
  have hlam0 : 0 ≤ 1 / 2 + (log x - log D') := by linarith
  set k := 10 * c0 / (3 * π ^ 2) with hk_def
  have hk0 : 0 < k := by positivity
  set lam := 1 / 2 + (log x - log D') with hlam_def
  have hLq : 0 ≤ log (2 * x) - log q := by
    have := Real.log_le_log hq0 hqx
    linarith
  have s1 : k * (q ^ 3 / x) * S ≤ k * (q ^ 3 / x) *
      ((log (2 * x) - log q) + (2 * D' / q + D' ^ 2 / (2 * q ^ 2)) * lam) :=
    mul_le_mul_of_nonneg_left hS (by positivity)
  have s2 : k * (q ^ 3 / x) *
      ((log (2 * x) - log q) + (2 * D' / q + D' ^ 2 / (2 * q ^ 2)) * lam) =
      k * (q ^ 3 / x * (log (2 * x) - log q)) + k * (2 * (q ^ 2 / x) * (D' * lam)) +
        k * (D' * q / x * (D' * lam) / 2) := by
    field_simp
    ring
  -- T1: `q³/x ≤ 2c₂q`
  have hq3 : q ^ 3 / x ≤ 2 * c2 * q := by
    rw [div_le_iff₀ hx0]
    have := mul_le_mul_of_nonneg_left hqq hq0.le
    linarith
  have t1 : q ^ 3 / x * (log (2 * x) - log q) ≤ 2 * c2 * q * (log (2 * x) - log q) :=
    mul_le_mul_of_nonneg_right hq3 hLq
  -- T2: `ψ(D') ≤ ψ(c₂x/q)`, as `c₂x/q ≤ x/√e` for `q ≥ 2`
  have he1 : exp (1 / 2) ≤ exp 1 := Real.exp_le_exp.mpr (by norm_num)
  have he9 := Real.exp_one_lt_d9
  have hcq : c2 * x / q ≤ x / exp (1 / 2) := by
    rw [div_le_div_iff₀ hq0 (Real.exp_pos _)]
    have h1 : c2 * exp (1 / 2) ≤ 2 := by
      have := mul_le_mul (le_of_lt hc2l) he1 (Real.exp_pos _).le (by norm_num)
      linarith
    have h2 : c2 * exp (1 / 2) * x ≤ q * x :=
      mul_le_mul_of_nonneg_right (h1.trans hq2) hx0.le
    linarith
  have hpsi := psiL_mono x D' (c2 * x / q) hx0 hD0 (by rw [le_div_iff₀ hq0]; exact hDq) hcq
  have hpsi' : D' * lam ≤ c2 * x / q * (1 / 2 + (log q - log c2)) := by
    unfold psiL at hpsi
    have hl : log (c2 * x / q) = log c2 + log x - log q := by
      rw [Real.log_div (by positivity) hq0.ne', Real.log_mul hc2.ne' hx0.ne']
    rw [hl] at hpsi
    have e1 : D' * lam = D' * (1 / 2 + log x - log D') := by rw [hlam_def]; ring
    have e2 : c2 * x / q * (1 / 2 + log x - (log c2 + log x - log q)) =
        c2 * x / q * (1 / 2 + (log q - log c2)) := by ring
    rw [e1, ← e2]
    exact hpsi
  have t2 : 2 * (q ^ 2 / x) * (D' * lam) ≤ 2 * c2 * q * (1 / 2 + (log q - log c2)) := by
    have := mul_le_mul_of_nonneg_left hpsi' (by positivity : (0 : ℝ) ≤ 2 * (q ^ 2 / x))
    refine this.trans (le_of_eq ?_)
    field_simp
  -- T3: `D'q/x ≤ c₂`
  have hDl : 0 ≤ D' * lam := mul_nonneg hD0.le hlam0
  have t3 : D' * q / x * (D' * lam) / 2 ≤ c2 * (D' * lam) / 2 := by
    have h1 : D' * q / x ≤ c2 := by rw [div_le_iff₀ hx0]; linarith
    have := mul_le_mul_of_nonneg_right h1 hDl
    linarith
  -- assembly
  have hsos : k * (c2 * (D' * lam) / 2) = 2 * √c0 / π * (D' * lam) := by
    rw [← sosot, hk_def]
    field_simp
    ring
  have hsq : q ≤ √(2 * c2 * x) := Real.le_sqrt_of_sq_le hqq
  have hRk : 20 * c0 * c2 ^ ((3 : ℝ) / 2) / (3 * π ^ 2) * √(2 * x) *
      log (2 * √(exp 1) * x / c2) =
      k * (2 * c2 * √(2 * c2 * x) * (1 / 2 + (log (2 * x) - log c2))) := by
    rw [hl5, hk_def]
    calc 20 * c0 * c2 ^ ((3 : ℝ) / 2) / (3 * π ^ 2) * √(2 * x) *
          (1 / 2 + (log (2 * x) - log c2)) =
        20 * c0 / (3 * π ^ 2) * (c2 ^ ((3 : ℝ) / 2) * √(2 * x)) *
          (1 / 2 + (log (2 * x) - log c2)) := by ring
      _ = 20 * c0 / (3 * π ^ 2) * (c2 * √(2 * c2 * x)) *
          (1 / 2 + (log (2 * x) - log c2)) := by rw [rpow_c2]
      _ = _ := by ring
  have hfin : k * (2 * c2 * q * (1 / 2 + (log (2 * x) - log c2))) ≤
      k * (2 * c2 * √(2 * c2 * x) * (1 / 2 + (log (2 * x) - log c2))) := by
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_ hM0) hk0.le
    exact mul_le_mul_of_nonneg_left hsq (by positivity)
  have hk1 := mul_le_mul_of_nonneg_left t1 hk0.le
  have hk2 := mul_le_mul_of_nonneg_left t2 hk0.le
  have hk3 := mul_le_mul_of_nonneg_left t3 hk0.le
  have hcomb : k * (2 * c2 * q * (log (2 * x) - log q)) +
      k * (2 * c2 * q * (1 / 2 + (log q - log c2))) =
      k * (2 * c2 * q * (1 / 2 + (log (2 * x) - log c2))) := by ring
  rw [hsos] at hk3
  rw [hRk]
  linarith

/-- **`eq:bocio`**: for `0 < D' ≤ min(c₂x/q, Q/2, x/4)`,
`∑_{q/2 < m ≤ D', q ∤ m} T ≤ (2√c₀/π)D' log(√e x/D') + (20c₀c₂^{3/2}/3π²)√(2x) log(2√e x/c₂)`. -/
theorem piece2L (x α β Q D' : ℝ) (a : ℤ) (q : ℕ) (hq : 1 ≤ q) (hcop : Int.gcd a q = 1)
    (hα : α = a / q + β / (q * Q)) (hβ : |β| ≤ 1) (hx : 4 ≤ x) (hD0 : 0 < D')
    (hDQ : 2 * D' ≤ Q) (hDc : D' ≤ c2 * x / q) (hDx : D' ≤ x / 4) (t : ℕ → ℝ)
    (ht : TBL x α t) :
    ∑ d ∈ (Ioc (q / 2) ⌊D'⌋₊).filter (fun d => ¬ q ∣ d), t d ≤
      2 * √c0 / π * (D' * (1 / 2 + (log x - log D'))) +
        20 * c0 * c2 ^ ((3 : ℝ) / 2) / (3 * π ^ 2) * √(2 * x) *
          log (2 * √(exp 1) * x / c2) := by
  have hx0 : 0 < x := by linarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hc0 := c0_pos
  have hc2 := c2_pos
  have hc2l := c2_lt
  have hpi := Real.pi_pos
  have hR0 : 0 ≤ 2 * √c0 / π * (D' * (1 / 2 + (log x - log D'))) +
      20 * c0 * c2 ^ ((3 : ℝ) / 2) / (3 * π ^ 2) * √(2 * x) * log (2 * √(exp 1) * x / c2) := by
    have hlD : log D' ≤ log x := Real.log_le_log hD0 (by linarith)
    have hlc2 : log c2 < 0 := Real.log_neg hc2 (by linarith)
    have hl2x : 0 ≤ log (2 * x) := Real.log_nonneg (by linarith)
    rw [log_2sqe x hx0]
    have h1 : 0 ≤ 2 * √c0 / π * (D' * (1 / 2 + (log x - log D'))) :=
      mul_nonneg (by positivity) (mul_nonneg hD0.le (by linarith))
    have h2 : 0 ≤ 20 * c0 * c2 ^ ((3 : ℝ) / 2) / (3 * π ^ 2) * √(2 * x) *
        (1 / 2 + (log (2 * x) - log c2)) := mul_nonneg (by positivity) (by linarith)
    linarith
  rcases Nat.lt_or_ge q 2 with hq1 | hq2
  · have hq1' : q = 1 := by omega
    have hemp : (Ioc (q / 2) ⌊D'⌋₊).filter (fun d => ¬ q ∣ d) = ∅ := by
      refine Finset.filter_false_of_mem fun d _ => ?_
      rw [hq1']
      exact not_not.mpr (one_dvd d)
    rw [hemp, Finset.sum_empty]
    exact hR0
  set h := q / 2 with hh_def
  set N := ⌊D'⌋₊ with hN_def
  set J := (N - h + q - 1) / q with hJ_def
  obtain ⟨hJ1, hJ2⟩ := cdiv_spec (N - h) q hq
  rw [← hJ_def] at hJ1 hJ2
  have hNJ : N ≤ h + J * q := by
    generalize J * q = P at hJ1 hJ2 ⊢
    omega
  have hhr : (h : ℝ) ≤ q / 2 := by
    rw [le_div_iff₀ (by norm_num)]
    have : q / 2 * 2 ≤ q := Nat.div_mul_le_self q 2
    exact_mod_cast this
  have hhr2 : ((q : ℝ) - 1) / 2 ≤ h := by
    have : q ≤ 2 * h + 1 := by omega
    have : (q : ℝ) ≤ 2 * h + 1 := by exact_mod_cast this
    linarith
  have hNr : (N : ℝ) ≤ D' := Nat.floor_le hD0.le
  rw [sum_filter_windows t _ h q J N hNJ]
  rcases Nat.eq_zero_or_pos J with hJ0 | hJ0
  · rw [hJ0, Finset.sum_range_zero]
    exact hR0
  have hNh : h + 1 ≤ N := by
    by_contra hcon
    have : N - h = 0 := by omega
    rw [this] at hJ_def
    have : J = 0 := by
      rw [hJ_def, zero_add]
      exact Nat.div_eq_of_lt (by omega)
    omega
  have hwin : ∀ j ∈ range J,
      ∑ d ∈ Ioc (h + j * q) (h + j * q + q), (if d ≤ N ∧ ¬ q ∣ d then t d else 0) ≤
        20 / (3 * π ^ 2) * ((log x - log (((j : ℝ) + 1 / 2) * q)) *
          (c0 * ((j : ℝ) + 3 / 2) * q / (2 * x))) * q ^ 2 := by
    intro j hj
    have hjJ : j + 1 ≤ J := Finset.mem_range.mp hj
    have hjq : h + j * q + 1 ≤ N := by
      have h1 := Nat.mul_le_mul_right q hjJ
      rw [add_mul, one_mul] at h1
      generalize j * q = P at h1 ⊢
      generalize J * q = P' at h1 hJ2
      omega
    exact cwinL x α β Q a q hq hcop hα hβ hx0 t ht h j N hhr hhr2 hjq (by linarith)
      (by linarith)
  refine (Finset.sum_le_sum hwin).trans ?_
  have e : ∑ j ∈ range J, 20 / (3 * π ^ 2) * ((log x - log (((j : ℝ) + 1 / 2) * q)) *
        (c0 * ((j : ℝ) + 3 / 2) * q / (2 * x))) * q ^ 2 =
      10 * c0 / (3 * π ^ 2) * ((q : ℝ) ^ 3 / x) *
        ∑ j ∈ range J, ((j : ℝ) + 3 / 2) * (log x - log (((j : ℝ) + 1 / 2) * q)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    field_simp
    ring
  rw [e]
  -- `J ≥ 1`: `q/2 < D' ≤ c₂x/q`, so `q² < 2c₂x`
  have hNh' : (h : ℝ) + 1 ≤ N := by exact_mod_cast hNh
  have hqD : (q : ℝ) / 2 < D' := by linarith
  have hDq : D' * q ≤ c2 * x := by rwa [le_div_iff₀ hq0] at hDc
  have hqq : (q : ℝ) ^ 2 ≤ 2 * c2 * x := by
    have h1 := mul_le_mul_of_nonneg_right hqD.le hq0.le
    have h2 : (q : ℝ) ^ 2 = 2 * (q / 2 * q) := by ring
    rw [h2]
    linarith
  have hJq : (J : ℝ) * q ≤ D' + q / 2 := by
    have h1 : J * q ≤ N - h + q - 1 := hJ2
    have h2 : J * q + h + 1 ≤ N + q := by
      generalize J * q = P at h1 ⊢
      omega
    have h4 : ((J * q + h + 1 : ℕ) : ℝ) ≤ ((N + q : ℕ) : ℝ) := by exact_mod_cast h2
    push_cast at h4
    linarith
  have he4 : exp 1 < 4 := by have := Real.exp_one_lt_d9; linarith
  have hDe : D' ≤ x / exp 1 := by
    rw [le_div_iff₀ (Real.exp_pos 1)]
    have := mul_le_mul_of_nonneg_left he4.le hD0.le
    linarith
  have hJ1' : (1 : ℕ) ≤ J := hJ0
  have hS := sumS x q D' J hx0 hq0 hJ1' (by linarith) hDe
  have hlq2 : log x - log ((q : ℝ) / 2) = log (2 * x) - log q := by
    rw [Real.log_div hq0.ne' (by norm_num), Real.log_mul (by norm_num) hx0.ne']
    ring
  rw [hlq2] at hS
  have hq2' : (2 : ℝ) ≤ q := by exact_mod_cast hq2
  exact p2_arith x q D' _ hx0 hq2' hD0 hDq hqq (by linarith) (by linarith) hS

/-! ## (6) Piece 3 -- `eq:caron` + `eq:binbed`, `R < m ≤ D` (`lem:gotog`) -/

/-- **One weighted `lem:gotog` window**: window `j` of `eq:caron` with weight
`log(x/(jq + R))`. -/
theorem gwinL (x α β Q D R : ℝ) (a : ℤ) (q : ℕ) (hq : 1 ≤ q) (hcop : Int.gcd a q = 1)
    (hα : α = a / q + β / (q * Q)) (hβ : |β| ≤ 1) (hqQ : (q : ℝ) ≤ Q) (hx : 0 < x)
    (hDx : D ≤ x / 4) (hR : 0 < R) (t : ℕ → ℝ) (ht : TBL x α t) (j : ℕ)
    (hj : (j : ℝ) * q + R ≤ D) :
    ∑ d ∈ Ioc (⌊R⌋₊ + j * q) (⌊R⌋₊ + j * q + q),
        (if d ≤ ⌊D⌋₊ ∧ True then t d else 0) ≤
      (log x - log (j * q + R)) * (3 * (c1 x D * x / (2 * (j * q + R))) +
        4 * q / π * √(c1 x D * x / (2 * (j * q + R)) * (c0 * ((j + 1) * q + R) / (2 * x)))) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hc0 := c0_pos
  have he := eta1_pos
  have hjr : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hjR : 0 < (j : ℝ) * q + R := by positivity
  have hD0 : 0 < D := lt_of_lt_of_le hjR hj
  have hc1 : 1 ≤ c1 x D := by
    unfold c1
    have : 0 ≤ eta1 * D / x := by positivity
    linarith
  have hc1' : 0 ≤ c1 x D := by linarith
  set Lj := log x - log (j * q + R) with hLj_def
  set A0 := c1 x D * x / (2 * (j * q + R)) with hA0
  set C0 := c0 * ((j + 1) * q + R) / (2 * x) with hC0
  have hLj : 0 ≤ Lj := by
    have := Real.log_le_log hjR (show (j : ℝ) * q + R ≤ x by linarith)
    linarith
  have hA00 : 0 ≤ A0 := by positivity
  have hC00 : 0 ≤ C0 := by positivity
  have hrR : (⌊R⌋₊ : ℝ) ≤ R := Nat.floor_le hR.le
  have hRr : R < ⌊R⌋₊ + 1 := Nat.lt_floor_add_one R
  have esq : √(Lj * A0 * (Lj * C0)) = Lj * √(A0 * C0) := by
    rw [show Lj * A0 * (Lj * C0) = Lj ^ 2 * (A0 * C0) by ring, Real.sqrt_mul (sq_nonneg _),
      Real.sqrt_sq hLj]
  refine (gotogN α β Q (Lj * A0) (Lj * C0) a q hq hcop hα hβ hqQ (mul_nonneg hLj hA00)
    (mul_nonneg hLj hC00) _ _ ?_ ?_).trans (le_of_eq ?_)
  · intro d hd
    have hd' := Finset.mem_Ioc.mp hd
    split_ifs with hdN
    · have hd1 : 1 ≤ d := by omega
      have hdr : (j : ℝ) * q + R ≤ d := by
        have : (⌊R⌋₊ : ℝ) + j * q + 1 ≤ d := by exact_mod_cast hd'.1
        linarith
      have hdx : (d : ℝ) ≤ x / 4 := by
        have : (d : ℝ) ≤ ⌊D⌋₊ := by exact_mod_cast hdN.1
        linarith [Nat.floor_le hD0.le]
      have hd0 : (0 : ℝ) < d := by linarith
      refine (ht d hd1 hdx).2.1.trans ?_
      have h1 : x / (2 * d) ≤ x / (2 * (j * q + R)) :=
        div_le_div_of_nonneg_left hx.le (by positivity) (by linarith)
      have h2 : eta1 / 2 ≤ eta1 * D / x * (x / (2 * (j * q + R))) := by
        rw [show eta1 * D / x * (x / (2 * (j * q + R))) = eta1 * D / (2 * (j * q + R)) by
          field_simp]
        rw [div_le_div_iff₀ (by norm_num) (by positivity)]
        nlinarith
      have e : A0 = x / (2 * (j * q + R)) + eta1 * D / x * (x / (2 * (j * q + R))) := by
        rw [hA0]
        unfold c1
        ring
      have hP : x / (2 * d) + eta1 / 2 ≤ A0 := by rw [e]; linarith
      exact mul_le_mul (log_div_le x d _ hx hjR hdr) hP (by positivity) hLj
    · exact mul_nonneg hLj hA00
  · intro d hd
    have hd' := Finset.mem_Ioc.mp hd
    split_ifs with hdN
    · have hd1 : 1 ≤ d := by omega
      have hdr : (j : ℝ) * q + R ≤ d := by
        have : (⌊R⌋₊ : ℝ) + j * q + 1 ≤ d := by exact_mod_cast hd'.1
        linarith
      have hdr2 : (d : ℝ) ≤ ((j : ℝ) + 1) * q + R := by
        have : (d : ℝ) ≤ ⌊R⌋₊ + j * q + q := by exact_mod_cast hd'.2
        linarith
      have hdx : (d : ℝ) ≤ x / 4 := by
        have : (d : ℝ) ≤ ⌊D⌋₊ := by exact_mod_cast hdN.1
        linarith [Nat.floor_le hD0.le]
      have hd0 : (0 : ℝ) < d := by linarith
      refine (ht d hd1 hdx).2.2.2.trans ?_
      have hCb : (d : ℝ) / x * (c0 / 2) ≤ C0 := by
        rw [hC0, div_mul_eq_mul_div, div_le_div_iff₀ hx (by positivity)]
        nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr hdr2) hc0.le) hx.le]
      exact mul_le_mul (log_div_le x d _ hx hjR hdr) hCb (by positivity) hLj
    · rw [zero_mul]
      exact mul_nonneg hLj hC00
  · rw [esq]
    ring

/-- **Window `j + 1` of `eq:caron`**: the weighted `lem:gotog` bound, with the weight of the
`1/(jq + R)` part raised to `log(x/R)`. -/
theorem p3_win (x α β Q D R : ℝ) (a : ℤ) (q : ℕ) (hq : 1 ≤ q) (hcop : Int.gcd a q = 1)
    (hα : α = a / q + β / (q * Q)) (hβ : |β| ≤ 1) (hqQ : (q : ℝ) ≤ Q) (hx : 0 < x)
    (hDx : D ≤ x / 4) (hR0 : 0 < R) (t : ℕ → ℝ) (ht : TBL x α t) (j : ℕ)
    (hjD : ((j : ℝ) + 1) * q + R ≤ D) :
    ∑ d ∈ Ioc (⌊R⌋₊ + (j + 1) * q) (⌊R⌋₊ + (j + 1) * q + q),
        (if d ≤ ⌊D⌋₊ ∧ True then t d else 0) ≤
      (log x - log R) * ((3 * c1 x D * x / 2 + 2 * q / π * √(c0 * c1 x D) * (q / 2)) *
        (1 / (((j : ℝ) + 1) * q + R))) +
        2 * √(c0 * c1 x D) / π * (q * (log x - log (((j : ℝ) + 1) * q + R))) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hc0 := c0_pos
  have he := eta1_pos
  have hpi := Real.pi_pos
  have hD0 : 0 < D := by
    have : (0 : ℝ) ≤ ((j : ℝ) + 1) * q := by positivity
    linarith
  have hc1' : 0 ≤ c1 x D := by
    unfold c1
    have : 0 ≤ eta1 * D / x := by positivity
    linarith
  set s := √(c0 * c1 x D) with hs_def
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have e1 : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
  have hg := gwinL x α β Q D R a q hq hcop hα hβ hqQ hx hDx hR0 t ht (j + 1) (by rw [e1]; exact hjD)
  have hsq := sqrt_ws x (c1 x D) R q j hx hc1' hq0 hR0
  rw [← hs_def] at hsq
  rw [e1] at hg hsq
  have hjr : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hjR : 0 < ((j : ℝ) + 1) * q + R := by positivity
  set coef := 3 * c1 x D * x / 2 + 2 * q / π * s * (q / 2) with hcoef_def
  have hin : 3 * (c1 x D * x / (2 * (((j : ℝ) + 1) * q + R))) +
      4 * q / π * √(c1 x D * x / (2 * (((j : ℝ) + 1) * q + R)) *
        (c0 * (((j : ℝ) + 1 + 1) * q + R) / (2 * x))) ≤
      coef * (1 / (((j : ℝ) + 1) * q + R)) + 2 * q / π * s := by
    have h4 := mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ 4 * q / π)
    have e : 3 * (c1 x D * x / (2 * (((j : ℝ) + 1) * q + R))) +
        4 * q / π * (s / 2 * (1 + q / (2 * (((j : ℝ) + 1) * q + R)))) =
        coef * (1 / (((j : ℝ) + 1) * q + R)) + 2 * q / π * s := by
      rw [hcoef_def]
      field_simp
      ring
    linarith
  have hLj : 0 ≤ log x - log (((j : ℝ) + 1) * q + R) := by
    have := Real.log_le_log hjR (show ((j : ℝ) + 1) * q + R ≤ x by linarith)
    linarith
  have hLL : log x - log (((j : ℝ) + 1) * q + R) ≤ log x - log R := by
    have h0 : (0 : ℝ) ≤ ((j : ℝ) + 1) * q := by positivity
    have := Real.log_le_log hR0 (show R ≤ ((j : ℝ) + 1) * q + R by linarith)
    linarith
  refine hg.trans ((mul_le_mul_of_nonneg_left hin hLj).trans ?_)
  have hc' : 0 ≤ coef * (1 / (((j : ℝ) + 1) * q + R)) := by positivity
  have h5 := mul_le_mul_of_nonneg_right hLL hc'
  have e3 : (log x - log (((j : ℝ) + 1) * q + R)) *
      (coef * (1 / (((j : ℝ) + 1) * q + R)) + 2 * q / π * s) =
      (log x - log (((j : ℝ) + 1) * q + R)) * (coef * (1 / (((j : ℝ) + 1) * q + R))) +
        2 * s / π * (q * (log x - log (((j : ℝ) + 1) * q + R))) := by ring
  linarith [e3]

/-- **The telescoped `√(1 + q/(jq+R))` part**: `∑_{j<K} q log(x/((j+1)q + R)) ≤ G(D) - G(R)`
for `Kq + R ≤ D ≤ x` (the book's `∫_R^D log(x/t) dt`). -/
theorem p3_tel (x q D R : ℝ) (K : ℕ) (hq : 0 < q) (hR : 0 < R) (hKD : (K : ℝ) * q + R ≤ D)
    (hDx : D ≤ x) :
    ∑ j ∈ range K, q * (log x - log (((j : ℝ) + 1) * q + R)) ≤ gG x D - gG x R := by
  have hstep : ∀ j ∈ range K, q * (log x - log (((j : ℝ) + 1) * q + R)) ≤
      gG x (((j + 1 : ℕ) : ℝ) * q + R) - gG x ((j : ℝ) * q + R) := by
    intro j _
    have hjr : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have h0 : 0 < (j : ℝ) * q + R := by positivity
    have := g_step x ((j : ℝ) * q + R) (((j : ℝ) + 1) * q + R) h0 (by linarith)
    have e : ((j : ℝ) + 1) * q + R - ((j : ℝ) * q + R) = q := by ring
    rw [e] at this
    have e1 : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
    rw [e1]
    exact this
  refine (Finset.sum_le_sum hstep).trans ?_
  rw [Finset.sum_range_sub (fun j => gG x ((j : ℝ) * q + R))]
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hKR : 0 < (K : ℝ) * q + R := by positivity
  have hK := g_step x ((K : ℝ) * q + R) D hKR hKD
  have hD0 : 0 < D := lt_of_lt_of_le hKR hKD
  have hDl : 0 ≤ log x - log D := by
    have := Real.log_le_log hD0 hDx
    linarith
  have e0 : ((0 : ℕ) : ℝ) * q + R = R := by push_cast; ring
  simp only [e0]
  have := mul_nonneg (sub_nonneg.mpr hKD) hDl
  linarith

/-- **The `j = 0` window's main term**: `log(x/R)·3c₁x/2R ≤ (3c₁/2)√(2x/c₂) log(2x/c₂)` (as
`x/R ≤ min(q/c₂, 2x/q) ≤ √(2x/c₂)`), and `log(x/R) ≤ log(q/c₂)`. -/
theorem p3_main0 (x q R c : ℝ) (hx : 0 < x) (hq : 1 ≤ q) (hc : 0 ≤ c) (hR1 : c2 * x / q ≤ R)
    (hR2 : q / 2 ≤ R) (hRx : R ≤ x) :
    (log x - log R) * (3 * (c * x / (2 * R))) ≤ 3 * c / 2 * √(2 * x / c2) * log (2 * x / c2) ∧
      log x - log R ≤ log q - log c2 := by
  have hq0 : 0 < q := by linarith
  have hc2 := c2_pos
  have hc2l := c2_lt
  have hR0 : 0 < R := lt_of_lt_of_le (by positivity) hR2
  have hLR : 0 ≤ log x - log R := by
    have := Real.log_le_log hR0 hRx
    linarith
  have hxR1 : x / R ≤ q / c2 := by
    rw [div_le_div_iff₀ hR0 hc2]
    rw [div_le_iff₀ hq0] at hR1
    linarith
  have hxR2 : x / R ≤ 2 * x / q := by
    rw [div_le_div_iff₀ hR0 hq0]
    have := mul_le_mul_of_nonneg_left hR2 hx.le
    linarith
  have hxW : x / R ≤ √(2 * x / c2) := by
    refine Real.le_sqrt_of_sq_le ?_
    have h1 := mul_le_mul hxR1 hxR2 (by positivity) (by positivity)
    have e : q / c2 * (2 * x / q) = 2 * x / c2 := by field_simp
    rw [e] at h1
    rw [sq]
    exact h1
  have hLRe : log x - log R = log (x / R) := (Real.log_div hx.ne' hR0.ne').symm
  have hx2 : 1 ≤ 2 * x / c2 := by
    rw [le_div_iff₀ hc2]
    have h1 : 1 ≤ x / R := by rw [le_div_iff₀ hR0]; linarith
    have h2 : (1 : ℝ) ≤ 2 * x / q := h1.trans hxR2
    rw [le_div_iff₀ hq0] at h2
    linarith
  have hl2x : 0 ≤ log (2 * x / c2) := Real.log_nonneg hx2
  have hlogW : log (x / R) ≤ log (2 * x / c2) := by
    have h1 := Real.log_le_log (by positivity) hxW
    rw [Real.log_sqrt (by positivity)] at h1
    linarith
  refine ⟨?_, ?_⟩
  · rw [hLRe]
    have e : log (x / R) * (3 * (c * x / (2 * R))) = 3 * c / 2 * (x / R * log (x / R)) := by
      field_simp
    rw [e, mul_assoc (3 * c / 2)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact mul_le_mul hxW hlogW (by rw [← hLRe]; exact hLR) (Real.sqrt_nonneg _)
  · rw [hLRe, ← Real.log_div hq0.ne' hc2.ne']
    exact Real.log_le_log (by positivity) hxR1

set_option maxHeartbeats 600000 in
/-- **`eq:caron` + `eq:binbed` for `lem:bostb1`**: for `R ≥ max(c₂x/q, q/2)` with `R < D ≤ x/4`,
`∑_{R < m ≤ D} T ≤ (3c₁/2)√(2x/c₂) log(2x/c₂) + log(q/c₂)·((2√(c₀c₁)/π)√3 q
+ (3c₁/2)(x/q)log⁺(D/(c₂x/q)) + (2√(c₀c₁)/π)(q/2)log⁺(D/(q/2))) + (2√(c₀c₁)/π)(G(D) - G(R))`. -/
theorem piece3L (x α β Q D R : ℝ) (a : ℤ) (q : ℕ) (hq : 1 ≤ q) (hcop : Int.gcd a q = 1)
    (hα : α = a / q + β / (q * Q)) (hβ : |β| ≤ 1) (hqQ : (q : ℝ) ≤ Q) (hx : 0 < x)
    (hDx : D ≤ x / 4) (hR1 : c2 * x / q ≤ R) (hR2 : (q : ℝ) / 2 ≤ R) (hRD : R < D)
    (t : ℕ → ℝ) (ht : TBL x α t) :
    ∑ d ∈ Ioc ⌊R⌋₊ ⌊D⌋₊, t d ≤
      3 * c1 x D / 2 * √(2 * x / c2) * log (2 * x / c2) +
        (log q - log c2) * (2 * √(c0 * c1 x D) / π * (√3 * q) +
          3 * c1 x D / 2 * (x / q) * logp (D / (c2 * x / q)) +
          2 * √(c0 * c1 x D) / π * (q / 2 * logp (D / (q / 2)))) +
        2 * √(c0 * c1 x D) / π * (gG x D - gG x R) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hc0 := c0_pos
  have hc2 := c2_pos
  have hc2l := c2_lt
  have hpi := Real.pi_pos
  have he := eta1_pos
  have hR0 : 0 < R := lt_of_lt_of_le (by positivity) hR2
  have hD0 : 0 < D := by linarith
  have hc1' : 0 ≤ c1 x D := by
    unfold c1
    have : 0 ≤ eta1 * D / x := by positivity
    linarith
  have hRx : R ≤ x := by linarith
  obtain ⟨hmain0, hLq⟩ := p3_main0 x q R (c1 x D) hx hq1 hc1' hR1 hR2 hRx
  set s := √(c0 * c1 x D) with hs_def
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hLR : 0 ≤ log x - log R := by
    have := Real.log_le_log hR0 hRx
    linarith
  have hqc : 0 ≤ log q - log c2 := by
    have := Real.log_le_log hc2 (show c2 ≤ q by linarith)
    linarith
  have hl2x : 0 ≤ log (2 * x / c2) :=
    Real.log_nonneg (by rw [le_div_iff₀ hc2]; linarith)
  have hlp1 : 0 ≤ logp (D / (c2 * x / q)) := le_max_right _ _
  have hlp2 : 0 ≤ logp (D / (q / 2)) := le_max_right _ _
  have hGD : 0 ≤ gG x D - gG x R := by
    have h1 := g_step x R D hR0 hRD.le
    have hDl : 0 ≤ log x - log D := by
      have := Real.log_le_log hD0 (by linarith : D ≤ x)
      linarith
    have := mul_nonneg (sub_nonneg.mpr hRD.le) hDl
    linarith
  have hRHS : 0 ≤ 3 * c1 x D / 2 * √(2 * x / c2) * log (2 * x / c2) +
      (log q - log c2) * (2 * s / π * (√3 * q) +
        3 * c1 x D / 2 * (x / q) * logp (D / (c2 * x / q)) +
        2 * s / π * (q / 2 * logp (D / (q / 2)))) +
      2 * s / π * (gG x D - gG x R) := by
    have h1 : 0 ≤ 3 * c1 x D / 2 * √(2 * x / c2) * log (2 * x / c2) :=
      mul_nonneg (by positivity) hl2x
    have h2 : 0 ≤ (log q - log c2) * (2 * s / π * (√3 * q) +
        3 * c1 x D / 2 * (x / q) * logp (D / (c2 * x / q)) +
        2 * s / π * (q / 2 * logp (D / (q / 2)))) := mul_nonneg hqc (by positivity)
    have h3 : 0 ≤ 2 * s / π * (gG x D - gG x R) := mul_nonneg (by positivity) hGD
    linarith
  set r := ⌊R⌋₊ with hr_def
  set N := ⌊D⌋₊ with hN_def
  set J := (N - r + q - 1) / q with hJ_def
  obtain ⟨hJ1, hJ2⟩ := cdiv_spec (N - r) q hq
  rw [← hJ_def] at hJ1 hJ2
  have hNJ : N ≤ r + J * q := by
    generalize J * q = P at hJ1 hJ2 ⊢
    omega
  have hfil : (Ioc r N).filter (fun _ => True) = Ioc r N :=
    Finset.filter_true_of_mem (fun _ _ => trivial)
  rw [← hfil, sum_filter_windows t (fun _ => True) r q J N hNJ]
  rcases Nat.eq_zero_or_pos J with hJ0 | hJ0
  · rw [hJ0]
    simpa using hRHS
  obtain ⟨K, hK⟩ : ∃ K, J = K + 1 := ⟨J - 1, by omega⟩
  have hNr : r + 1 ≤ N := by
    by_contra hcon
    have : N - r = 0 := by omega
    rw [this] at hJ_def
    have : J = 0 := by
      rw [hJ_def, zero_add]
      exact Nat.div_eq_of_lt (by omega)
    omega
  have hKr : (K : ℝ) * q + R ≤ D := by
    rw [hK] at hJ2
    have h1 : K * q + r + 1 ≤ N := by
      have e : (K + 1) * q = K * q + q := by ring
      rw [e] at hJ2
      generalize K * q = P at hJ2 ⊢
      omega
    have h2 : (K : ℝ) * q + r + 1 ≤ N := by exact_mod_cast h1
    have h3 : R < r + 1 := Nat.lt_floor_add_one R
    have h4 : (N : ℝ) ≤ D := Nat.floor_le (by linarith)
    linarith
  have hKr0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  rw [hK, Finset.sum_range_succ']
  set coef := 3 * c1 x D * x / 2 + 2 * q / π * s * (q / 2) with hcoef_def
  have hcoef : 0 ≤ coef := by positivity
  -- the `j + 1` windows
  have hwin : ∀ j ∈ range K,
      ∑ d ∈ Ioc (r + (j + 1) * q) (r + (j + 1) * q + q), (if d ≤ N ∧ True then t d else 0) ≤
        (log x - log R) * (coef * (1 / (((j : ℝ) + 1) * q + R))) +
          2 * s / π * (q * (log x - log (((j : ℝ) + 1) * q + R))) := by
    intro j hj
    have hjK : j + 1 ≤ K := Finset.mem_range.mp hj
    have hjK' : (j : ℝ) + 1 ≤ K := by exact_mod_cast hjK
    have hjD : ((j : ℝ) + 1) * q + R ≤ D := by
      have := mul_le_mul_of_nonneg_right hjK' hq0.le
      linarith
    exact p3_win x α β Q D R a q hq hcop hα hβ hqQ hx hDx hR0 t ht j hjD
  -- the `j = 0` window
  have hw0 := gwinL x α β Q D R a q hq hcop hα hβ hqQ hx hDx hR0 t ht 0
    (by have := mul_nonneg hKr0 hq0.le; push_cast; linarith)
  have hsq0 := sqrt_w0 x (c1 x D) R q hx hc1' (by linarith) hR0
  rw [← hs_def] at hsq0
  have h40 := mul_le_mul_of_nonneg_left hsq0 (by positivity : (0 : ℝ) ≤ 4 * q / π)
  have e00 : ((0 : ℕ) : ℝ) * q + R = R := by push_cast; ring
  rw [e00] at hw0 h40
  have hw0' : ∑ d ∈ Ioc (r + 0 * q) (r + 0 * q + q), (if d ≤ N ∧ True then t d else 0) ≤
      (log x - log R) * (3 * (c1 x D * x / (2 * R))) +
        (log x - log R) * (2 * s / π * (√3 * q)) := by
    refine hw0.trans ?_
    have e3 : 4 * q / π * (s / 2 * √3) = 2 * s / π * (√3 * q) := by ring
    rw [e3] at h40
    have h5 := mul_le_mul_of_nonneg_left h40 hLR
    linarith
  -- the harmonic part and the telescoped part
  have hsum := Finset.sum_le_sum hwin
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  have hH := harm_le q R hq0 hR0 K
  set H := ∑ j ∈ range K, 1 / (((j : ℝ) + 1) * q + R) with hH_def
  set Lg := Real.log ((K * q + R) / R) with hLg_def
  have hLg1 : Lg ≤ logp (D / (c2 * x / q)) := by
    refine log_le_logp _ _ (by positivity) ?_
    rw [div_le_div_iff₀ hR0 (by positivity)]
    have h1 : (K * q + R) * (c2 * x / q) ≤ (K * q + R) * R :=
      mul_le_mul_of_nonneg_left hR1 (by positivity)
    have h2 : (K * q + R) * R ≤ D * R := mul_le_mul_of_nonneg_right hKr hR0.le
    linarith
  have hLg2 : Lg ≤ logp (D / (q / 2)) := by
    refine log_le_logp _ _ (by positivity) ?_
    rw [div_le_div_iff₀ hR0 (by positivity)]
    have h1 : (K * q + R) * (q / 2) ≤ (K * q + R) * R :=
      mul_le_mul_of_nonneg_left hR2 (by positivity)
    have h2 : (K * q + R) * R ≤ D * R := mul_le_mul_of_nonneg_right hKr hR0.le
    linarith
  have hharm : (log x - log R) * (coef * H) ≤ (log q - log c2) *
      (3 * c1 x D / 2 * (x / q) * logp (D / (c2 * x / q)) +
        2 * s / π * (q / 2 * logp (D / (q / 2)))) := by
    have h1 : coef * H ≤ coef * (1 / q * Lg) := mul_le_mul_of_nonneg_left hH hcoef
    have e : coef * (1 / q * Lg) = 3 * c1 x D / 2 * (x / q) * Lg + 2 * s / π * (q / 2 * Lg) := by
      rw [hcoef_def]
      field_simp
    rw [e] at h1
    have h3 := mul_le_mul_of_nonneg_left hLg1 (by positivity : (0 : ℝ) ≤ 3 * c1 x D / 2 * (x / q))
    have h4 := mul_le_mul_of_nonneg_left hLg2 (by positivity : (0 : ℝ) ≤ q / 2)
    have h5 := mul_le_mul_of_nonneg_left h4 (by positivity : (0 : ℝ) ≤ 2 * s / π)
    have h2 : coef * H ≤ 3 * c1 x D / 2 * (x / q) * logp (D / (c2 * x / q)) +
        2 * s / π * (q / 2 * logp (D / (q / 2))) := by linarith
    have hH0 : 0 ≤ coef * H := mul_nonneg hcoef (Finset.sum_nonneg fun j _ => by positivity)
    exact mul_le_mul hLq h2 hH0 hqc
  have htel := p3_tel x q D R K hq0 hR0 hKr (by linarith)
  have htel2 := mul_le_mul_of_nonneg_left htel (by positivity : (0 : ℝ) ≤ 2 * s / π)
  have h0q : (log x - log R) * (2 * s / π * (√3 * q)) ≤
      (log q - log c2) * (2 * s / π * (√3 * q)) :=
    mul_le_mul_of_nonneg_right hLq (by positivity)
  linarith

/-! ## (7) The assembly: `eq:esthel2` ≤ `eq:kuche2` -/

/-- **`eq:esthel2` in the `eq:kuche2` case, for any `T` obeying the per-`m` estimate**: if
`2D' ≤ Q` and `D' ≤ M` for `D' = min(c₂x/q, D)`, then the `m ≤ D` other than (`q ∣ m` and
`m ≤ M`) contribute at most `eq:kuche2`. -/
theorem esthel_log (x α β Q D M : ℝ) (a : ℤ) (q : ℕ) (hq : 1 ≤ q) (hcop : Int.gcd a q = 1)
    (hα : α = a / q + β / (q * Q)) (hβ : |β| ≤ 1) (hqQ : (q : ℝ) ≤ Q) (hD : 1 ≤ D)
    (hDx : D ≤ x / 4) (hDQ : 2 * min (c2 * x / q) D ≤ Q) (hM : min (c2 * x / q) D ≤ M)
    (t : ℕ → ℝ) (ht : TBL x α t) :
    ∑ d ∈ (Ioc 0 ⌊D⌋₊).filter (fun d => ¬ (q ∣ d ∧ (d : ℝ) ≤ M)), t d ≤ kuche2 x q D := by
  have hx4 : 4 ≤ x := by linarith
  have hx : 0 < x := by linarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hc0 := c0_pos
  have hc2 := c2_pos
  have hc2l := c2_lt
  have hpi := Real.pi_pos
  have he := eta1_pos
  have hc1 : 1 ≤ c1 x D := by
    unfold c1
    have : 0 ≤ eta1 * D / x := by positivity
    linarith
  have hc1' : 0 ≤ c1 x D := by linarith
  set D' := min (c2 * x / q) D with hD'_def
  set R := max (c2 * x / q) ((q : ℝ) / 2) with hR_def
  have hD'0 : 0 < D' := lt_min (by positivity) (by linarith)
  have hD'c : D' ≤ c2 * x / q := min_le_left _ _
  have hD'D : D' ≤ D := min_le_right _ _
  have hR1 : c2 * x / q ≤ R := le_max_left _ _
  have hR2 : (q : ℝ) / 2 ≤ R := le_max_right _ _
  have hD'R : D' ≤ R := hD'c.trans hR1
  have hfl : ∀ d : ℕ, d ≤ ⌊D⌋₊ → (d : ℝ) ≤ x / 4 := by
    intro d hd
    have : (d : ℝ) ≤ ⌊D⌋₊ := by exact_mod_cast hd
    linarith [Nat.floor_le (by linarith : (0 : ℝ) ≤ D)]
  have hD'fl : ⌊D'⌋₊ ≤ ⌊D⌋₊ := Nat.floor_le_floor hD'D
  set f : ℕ → ℝ := fun d => if 1 ≤ d ∧ (d : ℝ) ≤ x / 4 then t d else 0 with hf_def
  have hf0 : ∀ d, 0 ≤ f d := by
    intro d
    simp only [hf_def]
    split_ifs with h
    · exact (ht d h.1 h.2).1
    · exact le_rfl
  have e0 : ∀ (S : Finset ℕ), (∀ d ∈ S, 1 ≤ d ∧ d ≤ ⌊D⌋₊) → ∑ d ∈ S, f d = ∑ d ∈ S, t d := by
    intro S hS
    refine Finset.sum_congr rfl fun d hd => ?_
    simp only [hf_def]
    rw [if_pos ⟨(hS d hd).1, hfl d (hS d hd).2⟩]
  -- the cover
  have hcov : (Ioc 0 ⌊D⌋₊).filter (fun d => ¬ (q ∣ d ∧ (d : ℝ) ≤ M)) ⊆
      (Ioc 0 (min (q / 2) ⌊D⌋₊) ∪ (Ioc (q / 2) ⌊D'⌋₊).filter (fun d => ¬ q ∣ d)) ∪
        Ioc ⌊R⌋₊ ⌊D⌋₊ := by
    intro d hd
    rw [Finset.mem_filter, Finset.mem_Ioc] at hd
    obtain ⟨⟨hd0, hdN⟩, hnot⟩ := hd
    rw [Finset.mem_union, Finset.mem_union, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Ioc,
      Finset.mem_Ioc]
    by_cases h1 : d ≤ q / 2
    · exact Or.inl (Or.inl ⟨hd0, le_min h1 hdN⟩)
    by_cases h2 : d ≤ ⌊D'⌋₊
    · refine Or.inl (Or.inr ⟨⟨by omega, h2⟩, fun hqd => hnot ⟨hqd, ?_⟩⟩)
      have : (d : ℝ) ≤ ⌊D'⌋₊ := by exact_mod_cast h2
      linarith [Nat.floor_le hD'0.le]
    · refine Or.inr ⟨?_, hdN⟩
      rw [Nat.floor_lt (by positivity)]
      have hDd : D' < d := (Nat.floor_lt hD'0.le).mp (by omega)
      have hdD : (d : ℝ) ≤ D := le_trans (by exact_mod_cast hdN) (Nat.floor_le (by linarith))
      have hcd : c2 * x / q < d := by
        rcases min_lt_iff.mp hDd with h | h
        · exact h
        · linarith
      have hqd : (q : ℝ) / 2 < d := by
        have : q < 2 * d := by omega
        have : (q : ℝ) < 2 * d := by exact_mod_cast this
        linarith
      exact max_lt hcd hqd
  have hS : ∑ d ∈ (Ioc 0 ⌊D⌋₊).filter (fun d => ¬ (q ∣ d ∧ (d : ℝ) ≤ M)), t d ≤
      ∑ d ∈ Ioc 0 (min (q / 2) ⌊D⌋₊), t d +
        ∑ d ∈ (Ioc (q / 2) ⌊D'⌋₊).filter (fun d => ¬ q ∣ d), t d +
        ∑ d ∈ Ioc ⌊R⌋₊ ⌊D⌋₊, t d := by
    have hsub := Finset.sum_le_sum_of_subset_of_nonneg hcov (f := f) (fun d _ _ => hf0 d)
    rw [e0 _ (fun d hd => by
      have := Finset.mem_Ioc.mp (Finset.mem_filter.mp hd).1
      exact ⟨this.1, this.2⟩)] at hsub
    refine hsub.trans ?_
    refine (sum_union_le_nn _ _ _ hf0).trans ?_
    refine add_le_add ((sum_union_le_nn _ _ _ hf0).trans (add_le_add ?_ ?_)) ?_
    · refine le_of_eq (e0 _ fun d hd => ?_)
      have := Finset.mem_Ioc.mp hd
      exact ⟨this.1, this.2.trans (min_le_right _ _)⟩
    · refine le_of_eq (e0 _ fun d hd => ?_)
      have := Finset.mem_Ioc.mp (Finset.mem_filter.mp hd).1
      exact ⟨by omega, this.2.trans hD'fl⟩
    · refine le_of_eq (e0 _ fun d hd => ?_)
      have := Finset.mem_Ioc.mp hd
      exact ⟨by omega, this.2⟩
  have h1 := piece1L x α β Q D a q hq hcop hα hβ hqQ (by linarith) (by linarith) hDx t ht
  have h2 := piece2L x α β Q D' a q hq hcop hα hβ hx4 hD'0 hDQ hD'c (hD'D.trans hDx) t ht
  refine hS.trans ?_
  -- the logarithms of `eq:kuche2`
  set s := √(c0 * c1 x D) with hs_def
  have hs1 : √c0 ≤ s := Real.sqrt_le_sqrt (le_mul_of_one_le_right hc0.le hc1)
  have hlexD : log (exp 1 * x / D) = 1 + log x - log D := by
    rw [Real.log_div (by positivity) (by linarith), Real.log_mul (Real.exp_pos 1).ne' hx.ne',
      Real.log_exp]
  have hlqc : log (q / c2) = log q - log c2 := Real.log_div hq0.ne' hc2.ne'
  have hgD : D * log (exp 1 * x / D) = gG x D := by
    rw [hlexD]
    unfold gG
    ring
  have hqc : 0 ≤ log q - log c2 := by
    have := Real.log_le_log hc2 (show c2 ≤ q by
      have : (1 : ℝ) ≤ q := by exact_mod_cast hq
      linarith)
    linarith
  have hx2 : 1 ≤ 2 * x / c2 := by
    rw [le_div_iff₀ hc2]
    nlinarith
  have hl2x : 0 ≤ log (2 * x / c2) := Real.log_nonneg hx2
  have hlp1 : 0 ≤ logp (D / (c2 * x / q)) := le_max_right _ _
  have hlp2 : 0 ≤ logp (D / (q / 2)) := le_max_right _ _
  -- `D'·log(√e x/D') ≤ G(D')`, and `G` increases
  have hlD' : log D' ≤ log x := Real.log_le_log hD'0 (by linarith)
  have hPG : D' * (1 / 2 + (log x - log D')) ≤ gG x D' := by
    unfold gG
    linarith
  have hP0 : 0 ≤ D' * (1 / 2 + (log x - log D')) := mul_nonneg hD'0.le (by linarith)
  have hgmono : ∀ u v : ℝ, 0 < u → u ≤ v → v ≤ x → gG x u ≤ gG x v := by
    intro u v hu huv hvx
    have := g_step x u v hu huv
    have hv : 0 < v := lt_of_lt_of_le hu huv
    have : 0 ≤ log x - log v := by
      have := Real.log_le_log hv hvx
      linarith
    linarith [mul_nonneg (sub_nonneg.mpr huv) this]
  have habs : ∀ v : ℝ, D' ≤ v → v ≤ x →
      2 * √c0 / π * (D' * (1 / 2 + (log x - log D'))) ≤ 2 * s / π * gG x v := by
    intro v hv hvx
    have h3 : D' * (1 / 2 + (log x - log D')) ≤ gG x v := hPG.trans (hgmono D' v hD'0 hv hvx)
    have h4 : 2 * √c0 / π ≤ 2 * s / π := by gcongr
    exact mul_le_mul h4 h3 hP0 (by positivity)
  have eK1 : 2 * s / π * D * log (exp 1 * x / D) = 2 * s / π * gG x D := by
    rw [← hgD]
    ring
  unfold kuche2
  rw [hlqc, ← hs_def]
  rcases lt_or_ge R D with hRD | hDR
  · have h3 := piece3L x α β Q D R a q hq hcop hα hβ hqQ hx hDx hR1 hR2 hRD t ht
    rw [← hs_def] at h3
    have hab := habs R hD'R (by linarith)
    linarith
  · have hemp : Ioc ⌊R⌋₊ ⌊D⌋₊ = ∅ := Finset.Ioc_eq_empty_of_le (Nat.floor_le_floor hDR)
    rw [hemp, Finset.sum_empty]
    have hab := habs D hD'D (by linarith)
    have hK3 : 0 ≤ 3 * c1 x D / 2 * (x / q) * logp (D / (c2 * x / q)) * (log q - log c2) :=
      mul_nonneg (by positivity) hqc
    have hK4 : 0 ≤ 2 * s / π * (√3 + logp (D / (q / 2)) / 2) * (log q - log c2) * q :=
      mul_nonneg (mul_nonneg (by positivity) hqc) hq0.le
    have hK5 : 0 ≤ 3 * c1 x D / 2 * √(2 * x / c2) * log (2 * x / c2) :=
      mul_nonneg (by positivity) hl2x
    linarith

/-- **`MPB1.EsthelLogEta2`, PROVED** (`esthel_log` at `α = 2β`, with `MPE2.approx_keks`). -/
theorem esthelLogEta2_holds : EsthelLogEta2 := by
  intro x α δ Q0 D a q hq hg h2 hδ hqQ hQ _hsq hD3 hDx hbr T hT
  have hD1 : 1 ≤ D := le_trans (Real.one_le_sqrt.mpr (by norm_num)) hD3
  have hx : 0 < x := by linarith
  obtain ⟨Q, β', hα, hβ', hqQ', hDQ, hM⟩ :=
    approx_keks x α δ Q0 D a q hq h2 hδ hqQ hQ hD1 (by linarith) hbr
  exact esthel_log x (2 * α) β' Q D (mR x δ q D) a q hq hg hα hβ' hqQ' hD1 hDx hDQ hM T
    (tbl_of_tromLB x α T hT)

/-- **`MPG.Bostb1Eta2` on the two cited computer checks alone, PROVED**
(`MPBL.bostb1Eta2_of_esthel` with `esthelLogEta2_holds`). -/
theorem bostb1Eta2_of_cited (hG : HC.CameloGridCited) (hW : HC.WollustCited) :
    MPG.Bostb1Eta2 :=
  MPBL.bostb1Eta2_of_esthel hG hW esthelLogEta2_holds

end Principia.Common.TernaryGoldbach.MPEL
