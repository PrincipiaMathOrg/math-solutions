/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Erdos1054.Spine
import Principia.Erdos1054.Basic
import Principia.Erdos1054.Density
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.Topology.Metrizable.Real

set_option autoImplicit false

/-!
# EP1054 §7 "The collision obstruction": the `Collision7` package of the spine

Paper `Campaigns/Erdos-1054/collab-paper/EP1054.tex`, lines 3028–3174
(`prop:dadd:collision-criterion` and the unlabeled proposition `liminf K_X(t) > 1/9`).
All sixteen obligations of the package are discharged.

Leaves (proved from the definitions and Mathlib alone):
* `leaf_Step_DaddCollisionArithmetic` — the exact rational `3492203725711/31001587618275 > 1/9`.
* `leaf_Step_DaddCollisionCores` — `(s(D), σ(D))` for `D ∈ {2,4,8,10}` and `Δ(5) = 4/15`.
* `leaf_Step_DaddCollisionH` — `∑_{(d,30)=1} d⁻² = 8π²/75` (Euler factors at `2, 3, 5` removed
  from `ζ(2) = π²/6`) and `H = 8π²/75 − 1 < 197/3675` (`π < 3.1416`).
* `leaf_Eq_DaddCollisionAffine` — `s(Du) = σ(D)σ(u) − Du = u(s(D) + σ(D)(h(u) − 1))`.

Links (proved from exactly the dependencies the spine names):
* `link_Step_DaddCollisionWitness`, `link_Step_DaddCollisionCombine`,
  `link_Step_DaddCollisionExplicit`, `link_Prop_DaddCollisionLowerBound` — the combinatorics
  and the final arithmetic of the lower bound;
* `link_Step_DaddCollisionSupport`, `link_Eq_DaddCollisionCriterion` — `ν_X([0,t]) =
  W*(t) − K_X(t) + o(1)`;
* `link_Prop_DaddCollisionCriterion` — the two equivalences, via Prokhorov compactness of the
  probability measures on `[0, ∞]`, their metrizability (Lévy–Prokhorov), the portmanteau theorem
  and the absence of finite atoms (`Thm_DaddUniversalSingularity_Carrier`);
* `link_Step_DaddCollisionCylinder`, `link_Step_DaddCollisionPerCore` — the cylinder `𝒯_D` and
  the per-core surplus;
* `link_Step_DaddCollisionFirstMoment` — the empirical divisor-sum expansion (Cesàro for the
  error term);
* `link_Step_DaddCollisionFirstMomentLaw` — layer cake, the Kovač third moment as the dominating
  function (`∫ (1 + s²)⁻¹ < ∞`) and dominated convergence;
* `link_Step_DaddCollisionSourceIntensity` — the radial partition argument (clamped test
  functions squeezing the indicator of `{x g(h) ≤ 1}`, Fubini against `1_{[0,1]} dx dν_{a,5}`)
  and Jensen in tangent-line form.
-/

namespace Principia.Erdos1054.Proofs.Collision7

open Finset Filter Real Principia.Erdos1054.Limits MeasureTheory
open scoped Topology ENNReal BoundedContinuousFunction

theorem sig_ge (n : ℕ) : n ≤ sig n := by
  show n ≤ ArithmeticFunction.sigma 1 n
  rw [ArithmeticFunction.sigma_one_apply]
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; exact Nat.zero_le _
  · exact Finset.single_le_sum (fun i _ => Nat.zero_le i) (Nat.mem_divisors_self n h.ne')

theorem coprime30_mod {u : ℕ} (h : Nat.Coprime u 30) : u % 2 = 1 ∧ u % 3 ≠ 0 ∧ u % 5 ≠ 0 := by
  have key : ∀ k : ℕ, 2 ≤ k → k ∣ 30 → ¬ k ∣ u := by
    intro k hk hk30 hku
    have h1 := Nat.dvd_gcd hku hk30
    rw [h.gcd_eq_one] at h1
    have := Nat.le_of_dvd one_pos h1
    omega
  refine ⟨?_, ?_, ?_⟩
  · have := key 2 le_rfl (by norm_num)
    omega
  · intro h3
    exact key 3 (by norm_num) (by norm_num) (Nat.dvd_of_mod_eq_zero h3)
  · intro h5
    exact key 5 (by norm_num) (by norm_num) (Nat.dvd_of_mod_eq_zero h5)

theorem coprime_core {D u : ℕ} (hD : D ∈ collisionCores) (hu : Nat.Coprime u 30) :
    Nat.Coprime D u := by
  have h3 : Nat.Coprime u (30 ^ 3) := Nat.Coprime.pow_right 3 hu
  have hdvd : D ∣ 30 ^ 3 := by
    simp only [collisionCores, Finset.mem_insert, Finset.mem_singleton] at hD
    rcases hD with rfl | rfl | rfl | rfl <;> norm_num
  exact (Nat.Coprime.coprime_dvd_right hdvd h3).symm

/-! ## Leaves -/

theorem arith : Step_DaddCollisionArithmetic := by
  unfold Step_DaddCollisionArithmetic
  constructor <;> norm_num

theorem sig_two : sig 2 = 3 := by decide
theorem sig_four : sig 4 = 7 := by decide
theorem sig_eight : sig 8 = 15 := by decide
theorem sig_ten : sig 10 = 18 := by decide

theorem delta_five : Delta 5 = 4 / 15 := by
  unfold Delta
  rw [show ⌊(5 : ℝ)⌋₊ = 5 from Nat.floor_ofNat 5]
  rw [show (Finset.range (5 + 1)).filter Nat.Prime = {2, 3, 5} by decide]
  norm_num

theorem cores : Step_DaddCollisionCores := by
  unfold Step_DaddCollisionCores
  refine ⟨?_, sig_two, ?_, sig_four, ?_, sig_eight, ?_, sig_ten, delta_five⟩
  · show sig 2 - 2 = 1; rw [sig_two]
  · show sig 4 - 4 = 3; rw [sig_four]
  · show sig 8 - 8 = 7; rw [sig_eight]
  · show sig 10 - 10 = 8; rw [sig_ten]

/-- The coprime-restricted `ζ(2)` summand. -/
noncomputable def zc (m : ℕ) (d : ℕ) : ℝ := if Nat.Coprime d m then (1 : ℝ) / (d : ℝ) ^ 2 else 0

theorem hasSum_zc_mul {m p : ℕ} {S : ℝ} (hp : p.Prime) (hpm : Nat.Coprime p m)
    (h : HasSum (zc m) S) : HasSum (zc (m * p)) ((1 - 1 / (p : ℝ) ^ 2) * S) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have h2 : HasSum (fun d => if p ∣ d then zc m d else 0) (1 / (p : ℝ) ^ 2 * S) := by
    have hinj : Function.Injective (fun k : ℕ => p * k) :=
      fun a b hab => Nat.eq_of_mul_eq_mul_left hp.pos hab
    rw [← hinj.hasSum_iff]
    · have hfun : (fun d => if p ∣ d then zc m d else 0) ∘ (fun k => p * k) =
          fun k => 1 / (p : ℝ) ^ 2 * zc m k := by
        funext k
        have hc : Nat.Coprime (p * k) m ↔ Nat.Coprime k m := by
          rw [Nat.coprime_mul_iff_left]
          exact ⟨fun h => h.2, fun h => ⟨hpm, h⟩⟩
        by_cases hk : Nat.Coprime k m
        · have hc' : Nat.Coprime (p * k) m := hc.2 hk
          show (if p ∣ p * k then zc m (p * k) else 0) = 1 / (p : ℝ) ^ 2 * zc m k
          rw [if_pos (dvd_mul_right p k)]
          unfold zc
          rw [if_pos hc', if_pos hk]
          push_cast
          rw [mul_pow, one_div_mul_one_div]
        · have hc' : ¬ Nat.Coprime (p * k) m := fun h => hk (hc.1 h)
          show (if p ∣ p * k then zc m (p * k) else 0) = 1 / (p : ℝ) ^ 2 * zc m k
          rw [if_pos (dvd_mul_right p k)]
          unfold zc
          rw [if_neg hc', if_neg hk, mul_zero]
      rw [hfun]
      exact h.mul_left _
    · intro x hx
      simp only [Set.mem_range, not_exists] at hx
      have : ¬ p ∣ x := by
        rintro ⟨k, rfl⟩
        exact hx k rfl
      simp [this]
  have hsub := h.sub h2
  have e1 : zc (m * p) = fun d => zc m d - (if p ∣ d then zc m d else 0) := by
    funext d
    by_cases hd : p ∣ d
    · have hnc : ¬ Nat.Coprime d (m * p) := by
        intro hc
        have hdp : Nat.Coprime d p := Nat.Coprime.coprime_dvd_right (dvd_mul_left p m) hc
        exact (hp.coprime_iff_not_dvd.1 hdp.symm) hd
      simp only [zc, hnc, if_false, hd, if_true, sub_self]
    · have hdp : Nat.Coprime d p := (hp.coprime_iff_not_dvd.2 hd).symm
      have hiff : Nat.Coprime d (m * p) ↔ Nat.Coprime d m := by
        rw [Nat.coprime_mul_iff_right]
        exact ⟨fun h => h.1, fun h => ⟨h, hdp⟩⟩
      simp only [zc, hiff, hd, if_false, sub_zero]
  have e2 : (1 - 1 / (p : ℝ) ^ 2) * S = S - 1 / (p : ℝ) ^ 2 * S := by ring
  rw [e1, e2]
  exact hsub

theorem hasSum_zc_thirty : HasSum (zc 30) (8 * Real.pi ^ 2 / 75) := by
  have h1 : HasSum (zc 1) (Real.pi ^ 2 / 6) := by
    have hf : zc 1 = fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2 := by
      funext d
      simp [zc]
    rw [hf]
    exact hasSum_zeta_two
  have h2 := hasSum_zc_mul (m := 1) (p := 2) Nat.prime_two (by norm_num) h1
  have h6 := hasSum_zc_mul (m := 1 * 2) (p := 3) Nat.prime_three (by norm_num) h2
  have h30 := hasSum_zc_mul (m := 1 * 2 * 3) (p := 5) Nat.prime_five (by norm_num) h6
  convert h30 using 1
  push_cast
  ring

theorem collisionH_lt : collisionH < 197 / 3675 := by
  unfold collisionH
  have h1 := Real.pi_lt_d4
  have h0 := Real.pi_pos
  nlinarith

theorem collisionH_pos : 0 < collisionH := by
  unfold collisionH
  have h1 := Real.pi_gt_d2
  nlinarith

theorem stepH : Step_DaddCollisionH := by
  unfold Step_DaddCollisionH
  exact ⟨hasSum_zc_thirty, collisionH_lt⟩

theorem affine : Eq_DaddCollisionAffine := by
  intro D hD u hu1 hu
  have hcop := coprime_core hD hu
  have hmul : sig (D * u) = sig D * sig u :=
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop
  have hge := sig_ge (D * u)
  have hgeD := sig_ge D
  refine ⟨?_, ?_⟩
  · show sig (D * u) - D * u + D * u = sig D * sig u
    rw [Nat.sub_add_cancel hge, hmul]
  · show ((sig (D * u) - D * u : ℕ) : ℝ) = u * (((sig D - D : ℕ) : ℝ) + sig D * (abundancy u - 1))
    rw [Nat.cast_sub hge, Nat.cast_sub hgeD, hmul, abundancy]
    have hu0 : (u : ℝ) ≠ 0 := by exact_mod_cast (show u ≠ 0 by omega)
    push_cast
    field_simp
    ring

theorem mem_cores {D : ℕ} (hD : D ∈ collisionCores) : D = 2 ∨ D = 4 ∨ D = 8 ∨ D = 10 := by
  simpa [collisionCores] using hD

theorem core_even {D : ℕ} (hD : D ∈ collisionCores) : 2 ∣ D := by
  rcases mem_cores hD with rfl | rfl | rfl | rfl <;> norm_num

theorem core_ge_two {D : ℕ} (hD : D ∈ collisionCores) : 2 ≤ D := by
  rcases mem_cores hD with rfl | rfl | rfl | rfl <;> norm_num

/-! ## Links -/

theorem witness_link : Principia.Erdos1054.Spine.Link_Step_DaddCollisionWitness := by
  intro hF2 D hD u hu1 _hu
  have hev : 2 ∣ D * u := dvd_mul_of_dvd_left (core_even hD) u
  have hd : 2 * (D * u / 2) = D * u := Nat.mul_div_cancel' hev
  have h2 : 2 ≤ D * u := le_trans (core_ge_two hD) (Nat.le_mul_of_pos_right D hu1)
  have hd1 : 1 ≤ D * u / 2 := by
    generalize D * u = n at *
    omega
  have hF := hF2 (D * u / 2) hd1
  rw [hd] at hF
  refine ⟨hF, ?_⟩
  have hge := F_ge 2 (D * u / 2) (by norm_num) hd1
  rw [hF] at hge
  generalize D * u = n at *
  omega

theorem core_mul_inj {D D' u u' : ℕ} (hD : D ∈ collisionCores) (hD' : D' ∈ collisionCores)
    (hu : Nat.Coprime u 30) (hu' : Nat.Coprime u' 30) (h : D * u = D' * u') :
    D = D' ∧ u = u' := by
  obtain ⟨a1, a2, a3⟩ := coprime30_mod hu
  obtain ⟨b1, b2, b3⟩ := coprime30_mod hu'
  rcases mem_cores hD with rfl | rfl | rfl | rfl <;>
    rcases mem_cores hD' with rfl | rfl | rfl | rfl <;> omega

theorem sum_cores_eq (f : ℕ → ℕ) :
    ∑ D ∈ collisionCores, f D = f 2 + (f 4 + (f 8 + f 10)) := by
  simp only [collisionCores]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]

theorem combine_link : Principia.Erdos1054.Spine.Link_Step_DaddCollisionCombine := by
  intro hW t ht N
  suffices hsum : rCore 2 N + rCore 4 N + rCore 8 N + rCore 10 N ≤ rtStar t N by
    rw [sum_cores_eq (fun D => rCore D N - 1)]
    omega
  classical
  let U : ℕ → Finset ℕ := fun D =>
    (Finset.Icc 1 N).filter (fun u => Nat.Coprime u 30 ∧ aliquot (D * u) = N)
  have hcard : (collisionCores.sigma U).card =
      rCore 2 N + rCore 4 N + rCore 8 N + rCore 10 N := by
    rw [Finset.card_sigma, sum_cores_eq (fun D => (U D).card)]
    simp only [U, rCore]
    ring
  rw [← hcard]
  unfold rtStar
  refine Finset.card_le_card_of_injOn (fun q => (2, q.1 * q.2 / 2)) ?_ ?_
  · rintro ⟨D, u⟩ hq
    rw [Finset.mem_coe, Finset.mem_sigma] at hq
    obtain ⟨hD, hu⟩ := hq
    simp only [U, Finset.mem_filter, Finset.mem_Icc] at hu
    obtain ⟨⟨hu1, huN⟩, hcop, hN⟩ := hu
    obtain ⟨hF, hle⟩ := hW D hD u hu1 hcop
    rw [hN] at hF hle
    have hev : 2 ∣ D * u := dvd_mul_of_dvd_left (core_even hD) u
    have hd : 2 * (D * u / 2) = D * u := Nat.mul_div_cancel' hev
    have h2 : 2 ≤ D * u := le_trans (core_ge_two hD) (Nat.le_mul_of_pos_right D hu1)
    have hN1 : 1 ≤ N := le_trans hu1 huN
    have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    have htN : (2 : ℝ) ≤ t * N := by nlinarith
    have hdle : D * u / 2 ≤ N := by
      generalize D * u = n at *
      omega
    have hdleR : ((D * u / 2 : ℕ) : ℝ) ≤ t * N := by
      have : ((D * u / 2 : ℕ) : ℝ) ≤ N := by exact_mod_cast hdle
      nlinarith
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
    refine ⟨⟨⟨le_rfl, Nat.le_floor (by exact_mod_cast htN)⟩, ?_, Nat.le_floor hdleR⟩, hF, ?_⟩
    · show 1 ≤ D * u / 2
      generalize D * u = n at *
      omega
    · show ((2 * (D * u / 2) : ℕ) : ℝ) ≤ t * N
      rw [hd]
      have : ((D * u : ℕ) : ℝ) ≤ 2 * N := by exact_mod_cast hle
      nlinarith
  · rintro ⟨D, u⟩ hq ⟨D', u'⟩ hq' heq
    rw [Finset.mem_coe, Finset.mem_sigma] at hq hq'
    simp only [U, Finset.mem_filter, Finset.mem_Icc] at hq hq'
    simp only [Prod.mk.injEq, true_and] at heq
    have hev : 2 ∣ D * u := dvd_mul_of_dvd_left (core_even hq.1) u
    have hev' : 2 ∣ D' * u' := dvd_mul_of_dvd_left (core_even hq'.1) u'
    have hd : 2 * (D * u / 2) = D * u := Nat.mul_div_cancel' hev
    have hd' : 2 * (D' * u' / 2) = D' * u' := Nat.mul_div_cancel' hev'
    have hmul : D * u = D' * u' := by rw [← hd, ← hd', heq]
    obtain ⟨rfl, rfl⟩ := core_mul_inj hq.1 hq'.1 hq.2.2.1 hq'.2.2.1 hmul
    rfl

theorem lowerBound_link : Principia.Erdos1054.Spine.Link_Prop_DaddCollisionLowerBound := by
  intro hE _hA t ht
  obtain ⟨c, hc, X₀, hX⟩ := hE t ht
  exact ⟨c, lt_trans (by norm_num) hc, X₀, hX⟩

/-- The per-core constant `Δ(5)(1/(s(D)+σ(D)H) − 1/D)` of `Step_DaddCollisionPerCore`. -/
noncomputable def coreTerm (D : ℕ) : ℝ :=
  Delta 5 * (1 / ((aliquot D : ℝ) + sig D * collisionH) - 1 / (D : ℝ))

theorem coreTerm_sum_gt (hCores : Step_DaddCollisionCores) (hH : Step_DaddCollisionH) :
    (3492203725711 / 31001587618275 : ℝ) < coreTerm 2 + coreTerm 4 + coreTerm 8 + coreTerm 10 := by
  obtain ⟨a2, s2, a4, s4, a8, s8, a10, s10, hD5⟩ := hCores
  have hHlt := hH.2
  have hHpos := collisionH_pos
  unfold coreTerm
  rw [a2, s2, a4, s4, a8, s8, a10, s10, hD5]
  have i2 : 1 / ((1 : ℝ) + 3 * (197 / 3675)) < 1 / ((1 : ℝ) + 3 * collisionH) :=
    one_div_lt_one_div_of_lt (by linarith) (by linarith)
  have i4 : 1 / ((3 : ℝ) + 7 * (197 / 3675)) < 1 / ((3 : ℝ) + 7 * collisionH) :=
    one_div_lt_one_div_of_lt (by linarith) (by linarith)
  have i8 : 1 / ((7 : ℝ) + 15 * (197 / 3675)) < 1 / ((7 : ℝ) + 15 * collisionH) :=
    one_div_lt_one_div_of_lt (by linarith) (by linarith)
  have i10 : 1 / ((8 : ℝ) + 18 * (197 / 3675)) < 1 / ((8 : ℝ) + 18 * collisionH) :=
    one_div_lt_one_div_of_lt (by linarith) (by linarith)
  have e : (4 / 15 : ℝ) * ((1 / ((1 : ℝ) + 3 * (197 / 3675)) - 1 / 2) +
      (1 / ((3 : ℝ) + 7 * (197 / 3675)) - 1 / 4) + (1 / ((7 : ℝ) + 15 * (197 / 3675)) - 1 / 8) +
      (1 / ((8 : ℝ) + 18 * (197 / 3675)) - 1 / 10)) = 3492203725711 / 31001587618275 := by
    norm_num
  push_cast
  linarith

theorem explicit_link : Principia.Erdos1054.Spine.Link_Step_DaddCollisionExplicit := by
  intro hPC hComb hCores hH _hArith t ht
  have hgt := coreTerm_sum_gt hCores hH
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = coreTerm 2 + coreTerm 4 + coreTerm 8 + coreTerm 10 := ⟨_, rfl⟩
  rw [← hL] at hgt
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = (L - 3492203725711 / 31001587618275) / 8 := ⟨_, rfl⟩
  have hεpos : 0 < ε := by rw [hε]; linarith
  obtain ⟨X2, hX2⟩ := hPC 2 (by decide) ε hεpos
  obtain ⟨X4, hX4⟩ := hPC 4 (by decide) ε hεpos
  obtain ⟨X8, hX8⟩ := hPC 8 (by decide) ε hεpos
  obtain ⟨X10, hX10⟩ := hPC 10 (by decide) ε hεpos
  refine ⟨L - 4 * ε, by rw [hε]; linarith,
    max 1 (max (max X2 X4) (max X8 X10)), fun X hX => ?_⟩
  have hX1 : 1 ≤ X := le_trans (le_max_left _ _) hX
  have hXa : max (max X2 X4) (max X8 X10) ≤ X := le_trans (le_max_right _ _) hX
  have b2 : coreTerm 2 - ε ≤ (1 / X) * ∑ N ∈ Finset.Icc 1 ⌊X⌋₊, ((rCore 2 N - 1 : ℕ) : ℝ) :=
    hX2 X (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hXa)
  have b4 : coreTerm 4 - ε ≤ (1 / X) * ∑ N ∈ Finset.Icc 1 ⌊X⌋₊, ((rCore 4 N - 1 : ℕ) : ℝ) :=
    hX4 X (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hXa)
  have b8 : coreTerm 8 - ε ≤ (1 / X) * ∑ N ∈ Finset.Icc 1 ⌊X⌋₊, ((rCore 8 N - 1 : ℕ) : ℝ) :=
    hX8 X (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hXa)
  have b10 : coreTerm 10 - ε ≤ (1 / X) * ∑ N ∈ Finset.Icc 1 ⌊X⌋₊, ((rCore 10 N - 1 : ℕ) : ℝ) :=
    hX10 X (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hXa)
  have hXinv : 0 ≤ 1 / X := by positivity
  have hkey : ∑ N ∈ Finset.Icc 1 ⌊X⌋₊,
      (((rCore 2 N - 1 : ℕ) : ℝ) + ((rCore 4 N - 1 : ℕ) : ℝ) + ((rCore 8 N - 1 : ℕ) : ℝ) +
        ((rCore 10 N - 1 : ℕ) : ℝ)) ≤ ∑ N ∈ Finset.Icc 1 ⌊X⌋₊, ((rtStar t N - 1 : ℕ) : ℝ) := by
    apply Finset.sum_le_sum
    intro N _
    have hc := hComb t ht N
    rw [sum_cores_eq (fun D => rCore D N - 1)] at hc
    have hc' : (((rCore 2 N - 1) + ((rCore 4 N - 1) + ((rCore 8 N - 1) + (rCore 10 N - 1))) : ℕ) :
        ℝ) ≤ ((rtStar t N - 1 : ℕ) : ℝ) := by exact_mod_cast hc
    rw [Nat.cast_add, Nat.cast_add, Nat.cast_add] at hc'
    linarith
  have hsplit : (1 / X) * ∑ N ∈ Finset.Icc 1 ⌊X⌋₊,
      (((rCore 2 N - 1 : ℕ) : ℝ) + ((rCore 4 N - 1 : ℕ) : ℝ) + ((rCore 8 N - 1 : ℕ) : ℝ) +
        ((rCore 10 N - 1 : ℕ) : ℝ)) =
      (1 / X) * ∑ N ∈ Finset.Icc 1 ⌊X⌋₊, ((rCore 2 N - 1 : ℕ) : ℝ) +
      (1 / X) * ∑ N ∈ Finset.Icc 1 ⌊X⌋₊, ((rCore 4 N - 1 : ℕ) : ℝ) +
      (1 / X) * ∑ N ∈ Finset.Icc 1 ⌊X⌋₊, ((rCore 8 N - 1 : ℕ) : ℝ) +
      (1 / X) * ∑ N ∈ Finset.Icc 1 ⌊X⌋₊, ((rCore 10 N - 1 : ℕ) : ℝ) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
    ring
  have hmono := mul_le_mul_of_nonneg_left hkey hXinv
  unfold KX
  linarith

/-! ## Real-`X` counting helpers -/

theorem tendsto_div_real_of_nat {s : ℕ → ℝ} {L : ℝ}
    (h : Tendsto (fun n : ℕ => s n / n) atTop (𝓝 L)) :
    Tendsto (fun X : ℝ => s ⌊X⌋₊ / X) atTop (𝓝 L) := by
  have h1 : Tendsto (fun X : ℝ => s ⌊X⌋₊ / (⌊X⌋₊ : ℝ)) atTop (𝓝 L) :=
    h.comp tendsto_nat_floor_atTop
  have h2 := h1.mul (tendsto_nat_floor_div_atTop (R := ℝ))
  rw [mul_one] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with X hX
  have hf : (0 : ℝ) < ⌊X⌋₊ := by exact_mod_cast Nat.floor_pos.2 hX
  have hX0 : (0 : ℝ) < X := by linarith
  field_simp

theorem hasDens_tendsto_real {S : Set ℕ} {d : ℝ} (h : HasDens S d) :
    Tendsto (fun X : ℝ => (cnt S X : ℝ) / X) atTop (𝓝 d) := by
  have := tendsto_div_real_of_nat (s := fun n : ℕ => (cnt S (n : ℝ) : ℝ)) h
  refine this.congr (fun X => ?_)
  simp only [cnt_floor]

theorem hasDens_of_tendsto_real {S : Set ℕ} {d : ℝ}
    (h : Tendsto (fun X : ℝ => (cnt S X : ℝ) / X) atTop (𝓝 d)) : HasDens S d :=
  h.comp tendsto_natCast_atTop_atTop

/-! ## `ν_X([0, t])` as a normalised count -/

theorem ratioE_le_iff {N : ℕ} {t : ℝ} (hN : 1 ≤ N) (ht : 0 ≤ t) :
    ratioE N ≤ ENNReal.ofReal t ↔ (f N : ℝ) ≤ t * N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  unfold ratioE
  rw [ENNReal.ofReal_le_ofReal_iff ht, div_le_iff₀ hNpos]

open Classical in
theorem nuX_Iic_real (X t : ℝ) (ht : 0 ≤ t) :
    (nuX X).real (Set.Iic (ENNReal.ofReal t)) =
      (cnt (smallRatioSet t) X : ℝ) / (Rcnt X : ℝ) := by
  have hmeas : MeasurableSet (Set.Iic (ENNReal.ofReal t)) := measurableSet_Iic
  have h1 : nuX X (Set.Iic (ENNReal.ofReal t)) =
      (Rcnt X : ℝ≥0∞)⁻¹ * (cnt (smallRatioSet t) X : ℝ≥0∞) := by
    rw [nuX, Measure.smul_apply, Measure.finsetSum_apply, smul_eq_mul, Finset.sum_filter]
    congr 1
    unfold cnt
    rw [Finset.natCast_card_filter]
    refine Finset.sum_congr rfl fun N hN => ?_
    have hN1 : 1 ≤ N := (Finset.mem_Icc.1 hN).1
    by_cases hR : N ∈ R
    · rw [if_pos hR, Measure.dirac_apply' _ hmeas]
      by_cases hle : (f N : ℝ) ≤ t * N
      · have hmem : ratioE N ∈ Set.Iic (ENNReal.ofReal t) := (ratioE_le_iff hN1 ht).2 hle
        have hS : N ∈ smallRatioSet t := ⟨hR, hle⟩
        rw [Set.indicator_of_mem hmem, if_pos hS]
        rfl
      · have hmem : ratioE N ∉ Set.Iic (ENNReal.ofReal t) :=
          fun h => hle ((ratioE_le_iff hN1 ht).1 h)
        have hS : N ∉ smallRatioSet t := fun h => hle h.2
        rw [Set.indicator_of_notMem hmem, if_neg hS]
    · have hS : N ∉ smallRatioSet t := fun h => hR h.1
      rw [if_neg hR, if_neg hS]
  rw [measureReal_def, h1, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    ENNReal.toReal_natCast, div_eq_inv_mul]

/-- `X / R(X) → 1`, from `R(X) = ⌊X⌋ − 2`. -/
theorem tendsto_Rcnt_div (hRc : Intro_RcntFormula) :
    Tendsto (fun X : ℝ => (Rcnt X : ℝ) / X) atTop (𝓝 1) := by
  have h1 : Tendsto (fun X : ℝ => (⌊X⌋₊ : ℝ) / X - 2 / X) atTop (𝓝 (1 - 0)) :=
    (tendsto_nat_floor_div_atTop (R := ℝ)).sub (tendsto_const_nhds.div_atTop tendsto_id)
  rw [sub_zero] at h1
  refine h1.congr' ?_
  filter_upwards [eventually_ge_atTop (5 : ℝ)] with X hX
  have hfl : 5 ≤ ⌊X⌋₊ := Nat.le_floor (by exact_mod_cast hX)
  rw [hRc X hX, Nat.cast_sub (by omega), sub_div]
  norm_num

theorem sig_eq_F_one (n : ℕ) : sig n = F 1 n := by
  show ArithmeticFunction.sigma 1 n = F 1 n
  rw [ArithmeticFunction.sigma_one_apply, F, one_mul, Finset.filter_true_of_mem]
  intro d hd
  exact Nat.divisor_le hd

open Classical in
theorem cnt_rtStar_pos (t X : ℝ) :
    (((Finset.Icc 1 ⌊X⌋₊).filter (fun N : ℕ => 0 < rtStar t N)).card : ℕ) =
      cnt {N : ℕ | 0 < rtStar t N} X := by
  unfold cnt
  congr 1
  ext N
  simp only [Finset.mem_filter, Set.mem_setOf_eq]

/-- `r*_t(N) > 0 ⟹ N ∈ 𝓡, f(N) ≤ t N`. -/
theorem smallRatio_of_rtStar_pos {t : ℝ} {N : ℕ} (h : 0 < rtStar t N) : N ∈ smallRatioSet t := by
  unfold rtStar at h
  obtain ⟨p, hp⟩ := Finset.card_pos.1 h
  rw [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hp
  obtain ⟨⟨⟨he2, _⟩, hd1, _⟩, hF, hle⟩ := hp
  have hR : N ∈ R := (mem_R_iff_exists_F N).2 ⟨p.1, p.2, by omega, hd1, hF.symm⟩
  refine ⟨hR, ?_⟩
  have := f_le_of_F p.1 p.2 N (by omega) hd1 hF.symm
  have h' : ((f N : ℕ) : ℝ) ≤ ((p.1 * p.2 : ℕ) : ℝ) := by exact_mod_cast this
  linarith

/-- A small-ratio target with no proper witness lies in `σ(ℕ)`. -/
theorem mem_sigRange_of_smallRatio {t : ℝ} {N : ℕ} (hA : N ∈ smallRatioSet t)
    (hB : ¬ 0 < rtStar t N) : ∃ n : ℕ, 1 ≤ n ∧ sig n = N := by
  obtain ⟨hR, hle⟩ := hA
  obtain ⟨e, d, he, hd, hf, hN⟩ := f_mem_Fform N hR
  rcases Nat.lt_or_ge e 2 with he2 | he2
  · have : e = 1 := by omega
    subst this
    exact ⟨d, hd, by rw [sig_eq_F_one, hN]⟩
  · exfalso
    apply hB
    unfold rtStar
    apply Finset.card_pos.2
    refine ⟨(e, d), ?_⟩
    have hedR : ((e * d : ℕ) : ℝ) ≤ t * N := by rw [← hf]; exact hle
    have heR : (e : ℝ) ≤ t * N := by
      have : e ≤ e * d := Nat.le_mul_of_pos_right e hd
      have : (e : ℝ) ≤ ((e * d : ℕ) : ℝ) := by exact_mod_cast this
      linarith
    have hdR : (d : ℝ) ≤ t * N := by
      have : d ≤ e * d := Nat.le_mul_of_pos_left d (by omega)
      have : (d : ℝ) ≤ ((e * d : ℕ) : ℝ) := by exact_mod_cast this
      linarith
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
    exact ⟨⟨⟨he2, Nat.le_floor heR⟩, hd, Nat.le_floor hdR⟩, hN.symm, hedR⟩

/-- `ν_X([0, t]) − #{N ≤ X : N ∈ 𝓡, f(N) ≤ tN}/X → 0`, from `R(X) = ⌊X⌋ − 2`. -/
theorem tendsto_nuX_sub_cnt (hRc : Intro_RcntFormula) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun X : ℝ => (nuX X).real (Set.Iic (ENNReal.ofReal t)) -
      (cnt (smallRatioSet t) X : ℝ) / X) atTop (𝓝 0) := by
  set A := smallRatioSet t with hAdef
  have hR1 := tendsto_Rcnt_div hRc
  have hinv : Tendsto (fun X : ℝ => X / (Rcnt X : ℝ) - 1) atTop (𝓝 0) := by
    have := hR1.inv₀ one_ne_zero
    rw [inv_one] at this
    have := this.sub_const 1
    rw [sub_self] at this
    refine this.congr (fun X => ?_)
    rw [inv_div]
  refine squeeze_zero_norm' ?_ (hinv.norm.trans_eq (by rw [norm_zero]))
  filter_upwards [eventually_ge_atTop (5 : ℝ)] with X hX
  have hXpos : (0 : ℝ) < X := by linarith
  have hfl : 5 ≤ ⌊X⌋₊ := Nat.le_floor (by exact_mod_cast hX)
  have hRpos : (0 : ℝ) < Rcnt X := by
    rw [hRc X hX]
    have : 0 < ⌊X⌋₊ - 2 := by omega
    exact_mod_cast this
  have hA0 : (0 : ℝ) ≤ cnt A X := Nat.cast_nonneg _
  have hA1 : (cnt A X : ℝ) ≤ X := by
    have := cnt_le_floor A X
    have h' : (cnt A X : ℝ) ≤ ⌊X⌋₊ := by exact_mod_cast this
    linarith [Nat.floor_le hXpos.le]
  rw [nuX_Iic_real X t ht]
  have e : (cnt A X : ℝ) / (Rcnt X : ℝ) - (cnt A X : ℝ) / X =
      ((cnt A X : ℝ) / X) * (X / (Rcnt X : ℝ) - 1) := by
    field_simp
  rw [e, norm_mul]
  have hq : ‖(cnt A X : ℝ) / X‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hA0 hXpos.le)]
    exact (div_le_one hXpos).2 hA1
  calc ‖(cnt A X : ℝ) / X‖ * ‖X / (Rcnt X : ℝ) - 1‖ ≤ 1 * ‖X / (Rcnt X : ℝ) - 1‖ :=
        mul_le_mul_of_nonneg_right hq (norm_nonneg _)
    _ = ‖X / (Rcnt X : ℝ) - 1‖ := one_mul _

theorem support_link : Principia.Erdos1054.Spine.Link_Step_DaddCollisionSupport := by
  intro hSR hRc _hPos t ht
  set A := smallRatioSet t with hAdef
  set B : Set ℕ := {N : ℕ | 0 < rtStar t N} with hBdef
  set Sg : Set ℕ := {N : ℕ | ∃ n : ℕ, 1 ≤ n ∧ sig n = N} with hSgdef
  have hBA : B ⊆ A := fun N hN => smallRatio_of_rtStar_pos hN
  have hAB : A ⊆ B ∪ Sg := by
    intro N hN
    by_cases hB : 0 < rtStar t N
    · exact Or.inl hB
    · exact Or.inr (mem_sigRange_of_smallRatio hN hB)
  -- the count difference is `o(X)`
  have hSgR : Tendsto (fun X : ℝ => (cnt Sg X : ℝ) / X) atTop (𝓝 0) := hasDens_tendsto_real hSR
  have hdiff : Tendsto (fun X : ℝ => (cnt A X : ℝ) / X - (cnt B X : ℝ) / X) atTop (𝓝 0) := by
    refine squeeze_zero' ?_ ?_ hSgR
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
      have := cnt_mono hBA X
      have : (cnt B X : ℝ) ≤ cnt A X := by exact_mod_cast this
      rw [← sub_div]
      exact div_nonneg (by linarith) hX.le
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
      have h1 := cnt_le_cnt_add_of_subset_union hAB X
      have h1' : (cnt A X : ℝ) ≤ cnt B X + cnt Sg X := by exact_mod_cast h1
      rw [← sub_div]
      exact div_le_div_of_nonneg_right (by linarith) hX.le
  have hnu := tendsto_nuX_sub_cnt hRc ht.le
  have hsum := hnu.add hdiff
  rw [add_zero] at hsum
  refine hsum.congr (fun X => ?_)
  rw [cnt_rtStar_pos]
  ring

theorem eqCriterion_link : Principia.Erdos1054.Spine.Link_Eq_DaddCollisionCriterion := by
  intro hSup hWM t ht
  have h1 := hSup t ht
  have h2 := (hWM.1 t ht).2.1
  have h2' : Tendsto (fun X : ℝ => (1 / X) * ∑ N ∈ Finset.Icc 1 ⌊X⌋₊, (rtStar t N : ℝ) -
      WstarFun t) atTop (𝓝 0) := tendsto_sub_nhds_zero_iff.2 h2
  have h3 := h1.add h2'
  rw [add_zero] at h3
  refine h3.congr (fun X => ?_)
  have hsum : ∑ N ∈ Finset.Icc 1 ⌊X⌋₊, (rtStar t N : ℝ) =
      ((((Finset.Icc 1 ⌊X⌋₊).filter (fun N : ℕ => 0 < rtStar t N)).card : ℕ) : ℝ) +
        ∑ N ∈ Finset.Icc 1 ⌊X⌋₊, ((rtStar t N - 1 : ℕ) : ℝ) := by
    rw [Finset.natCast_card_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun N _ => ?_
    rcases Nat.eq_zero_or_pos (rtStar t N) with h | h
    · rw [h]
      simp
    · rw [if_pos h, Nat.cast_sub h]
      push_cast
      ring
  unfold KX
  rw [hsum]
  ring

/-! ## The cylinder -/

theorem coprime_of_add {m u : ℕ} (hu : Nat.Coprime u 30) (h : 30 ∣ m + u) :
    Nat.Coprime m 30 := by
  have g1 : Nat.gcd m 30 ∣ m := Nat.gcd_dvd_left m 30
  have g2 : Nat.gcd m 30 ∣ 30 := Nat.gcd_dvd_right m 30
  have g3 : Nat.gcd m 30 ∣ u := (Nat.dvd_add_right g1).1 (dvd_trans g2 h)
  have g4 : Nat.gcd m 30 ∣ Nat.gcd u 30 := Nat.dvd_gcd g3 g2
  rw [hu.gcd_eq_one] at g4
  exact Nat.eq_one_of_dvd_one g4

/-- If `1200 ∣ σ(Du)` then the target `s(Du)` lies in the cylinder `𝒯_D`. -/
theorem cyl_of_dvd {D u : ℕ} (hD : D ∈ collisionCores) (hu : Nat.Coprime u 30)
    (h : 1200 ∣ sig (D * u)) : D ∣ aliquot (D * u) ∧ Nat.Coprime (aliquot (D * u) / D) 30 := by
  obtain ⟨k, hk⟩ := h
  have hge := sig_ge (D * u)
  show D ∣ sig (D * u) - D * u ∧ Nat.Coprime ((sig (D * u) - D * u) / D) 30
  generalize hs : sig (D * u) = s at hk hge
  subst hk
  rcases mem_cores hD with rfl | rfl | rfl | rfl <;>
    exact ⟨Nat.dvd_of_mod_eq_zero (by omega), coprime_of_add hu (Nat.dvd_of_mod_eq_zero (by omega))⟩

theorem exc_card_le {D : ℕ} (hD : D ∈ collisionCores) (X : ℝ) :
    ((Finset.Icc 1 ⌊X⌋₊).filter (fun u : ℕ => Nat.Coprime u 30 ∧ (aliquot (D * u) : ℝ) ≤ X ∧
        ¬ (D ∣ aliquot (D * u) ∧ Nat.Coprime (aliquot (D * u) / D) 30))).card ≤
      cnt {n : ℕ | ¬ 1200 ∣ sig n} (D * X) := by
  classical
  have hDpos : 0 < D := by have := core_ge_two hD; omega
  unfold cnt
  refine Finset.card_le_card_of_injOn (fun u => D * u) ?_ ?_
  · intro u hu
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hu
    obtain ⟨⟨hu1, huX⟩, hcop, _, hbad⟩ := hu
    rw [Finset.mem_coe, mem_cntFinset]
    have hX1 : (1 : ℝ) ≤ X := Nat.floor_pos.1 (by omega)
    have huR : (u : ℝ) ≤ X :=
      le_trans (by exact_mod_cast huX) (Nat.floor_le (by linarith))
    refine ⟨⟨Nat.mul_pos hDpos hu1, Nat.le_floor ?_⟩, ?_⟩
    · push_cast
      exact mul_le_mul_of_nonneg_left huR (Nat.cast_nonneg D)
    · show ¬ 1200 ∣ sig (D * u)
      exact fun h => hbad (cyl_of_dvd hD hcop h)
  · intro a _ b _ hab
    exact Nat.eq_of_mul_eq_mul_left hDpos hab

theorem cnt_cyl {D : ℕ} (hD : D ∈ collisionCores) :
    cnt {N : ℕ | D ∣ N ∧ Nat.Coprime (N / D) 30} ((30 * D : ℕ) : ℝ) = 8 := by
  rw [cnt_natCast]
  rcases mem_cores hD with rfl | rfl | rfl | rfl
  · have h : ((Finset.Icc 1 (30 * 2)).filter (fun N => 2 ∣ N ∧ Nat.Coprime (N / 2) 30)).card = 8 := by
      decide
    refine Eq.trans ?_ h
    congr 1
    ext N
    simp only [Finset.mem_filter, Set.mem_setOf_eq]
  · have h : ((Finset.Icc 1 (30 * 4)).filter (fun N => 4 ∣ N ∧ Nat.Coprime (N / 4) 30)).card = 8 := by
      decide
    refine Eq.trans ?_ h
    congr 1
    ext N
    simp only [Finset.mem_filter, Set.mem_setOf_eq]
  · have h : ((Finset.Icc 1 (30 * 8)).filter (fun N => 8 ∣ N ∧ Nat.Coprime (N / 8) 30)).card = 8 := by
      decide
    refine Eq.trans ?_ h
    congr 1
    ext N
    simp only [Finset.mem_filter, Set.mem_setOf_eq]
  · have h : ((Finset.Icc 1 (30 * 10)).filter
        (fun N => 10 ∣ N ∧ Nat.Coprime (N / 10) 30)).card = 8 := by
      decide
    refine Eq.trans ?_ h
    congr 1
    ext N
    simp only [Finset.mem_filter, Set.mem_setOf_eq]

theorem cylinder_link : Principia.Erdos1054.Spine.Link_Step_DaddCollisionCylinder := by
  intro hFMN _hDelta D hD
  have hDpos : 0 < D := by have := core_ge_two hD; omega
  have hDR : (0 : ℝ) < D := by exact_mod_cast hDpos
  refine ⟨?_, ?_⟩
  · have hV : DensZero {n : ℕ | ¬ 1200 ∣ sig n} := hFMN 1200 (by norm_num)
    have hVR := hasDens_tendsto_real hV
    have hcomp : Tendsto (fun X : ℝ => (cnt {n : ℕ | ¬ 1200 ∣ sig n} (D * X) : ℝ) / (D * X))
        atTop (𝓝 0) := hVR.comp (tendsto_id.const_mul_atTop hDR)
    have hmul := hcomp.const_mul (D : ℝ)
    rw [mul_zero] at hmul
    refine squeeze_zero' ?_ ?_ hmul
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
      positivity
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
      have h1 := exc_card_le hD X
      have h1' : (((Finset.Icc 1 ⌊X⌋₊).filter (fun u : ℕ => Nat.Coprime u 30 ∧
          (aliquot (D * u) : ℝ) ≤ X ∧
          ¬ (D ∣ aliquot (D * u) ∧ Nat.Coprime (aliquot (D * u) / D) 30))).card : ℝ) ≤
          (cnt {n : ℕ | ¬ 1200 ∣ sig n} (D * X) : ℝ) := by exact_mod_cast h1
      have e : (D : ℝ) * ((cnt {n : ℕ | ¬ 1200 ∣ sig n} (D * X) : ℝ) / (D * X)) =
          (1 / X) * (cnt {n : ℕ | ¬ 1200 ∣ sig n} (D * X) : ℝ) := by
        field_simp
      rw [e]
      exact mul_le_mul_of_nonneg_left h1' (by positivity)
  · have hQ : 0 < 30 * D := by omega
    have hper : ∀ N, N + 30 * D ∈ {N : ℕ | D ∣ N ∧ Nat.Coprime (N / D) 30} ↔
        N ∈ {N : ℕ | D ∣ N ∧ Nat.Coprime (N / D) 30} := by
      intro N
      simp only [Set.mem_setOf_eq]
      rw [Nat.dvd_add_left (Dvd.intro_left 30 rfl)]
      constructor
      · rintro ⟨hdvd, hc⟩
        refine ⟨hdvd, ?_⟩
        rwa [Nat.add_mul_div_right N 30 hDpos, Nat.coprime_add_self_left] at hc
      · rintro ⟨hdvd, hc⟩
        refine ⟨hdvd, ?_⟩
        rwa [Nat.add_mul_div_right N 30 hDpos, Nat.coprime_add_self_left]
    have h := hasDens_of_periodic hQ hper
    rw [cnt_cyl hD] at h
    convert h using 1
    rw [delta_five]
    push_cast
    field_simp
    norm_num

/-! ## Per core -/

/-- `σ(2m) ≥ 3m`: the divisors `m` and `2m`. -/
theorem sig_two_mul_ge (m : ℕ) (hm : 1 ≤ m) : 3 * m ≤ sig (2 * m) := by
  show 3 * m ≤ ArithmeticFunction.sigma 1 (2 * m)
  rw [ArithmeticFunction.sigma_one_apply]
  have hsub : ({m, 2 * m} : Finset ℕ) ⊆ (2 * m).divisors := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Nat.mem_divisors]
    rcases hx with rfl | rfl
    · exact ⟨Dvd.intro_left 2 rfl, by omega⟩
    · exact ⟨dvd_rfl, by omega⟩
  have := Finset.sum_le_sum_of_subset (f := fun d : ℕ => d) hsub
  rw [Finset.sum_pair (by omega)] at this
  omega

/-- `u ≤ s(Du)` for a core `D` (`s(Du) ≥ Du/2 ≥ u`). -/
theorem le_aliquot_core {D u : ℕ} (hD : D ∈ collisionCores) (hu : 1 ≤ u) : u ≤ aliquot (D * u) := by
  have hev : 2 ∣ D * u := dvd_mul_of_dvd_left (core_even hD) u
  have hd : 2 * (D * u / 2) = D * u := Nat.mul_div_cancel' hev
  have h2 : 2 * u ≤ D * u := Nat.mul_le_mul_right u (core_ge_two hD)
  have hm1 : 1 ≤ D * u / 2 := by
    generalize D * u = n at *
    omega
  have hs := sig_two_mul_ge (D * u / 2) hm1
  rw [hd] at hs
  show u ≤ sig (D * u) - D * u
  generalize D * u = n at *
  omega

/-- `∑_{N ≤ X} r_D(N)` is the number of parameters `u` with `s(Du) ≤ X`. -/
theorem sum_rCore_eq {D : ℕ} (hD : D ∈ collisionCores) (X : ℝ) :
    ∑ N ∈ Finset.Icc 1 ⌊X⌋₊, rCore D N =
      ((Finset.Icc 1 ⌊X⌋₊).filter (fun u : ℕ =>
          Nat.Coprime u 30 ∧ (aliquot (D * u) : ℝ) ≤ X)).card := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := fun u => aliquot (D * u)) (t := Finset.Icc 1 ⌊X⌋₊)]
  · refine Finset.sum_congr rfl fun N hN => ?_
    rw [Finset.mem_Icc] at hN
    have hX1 : (1 : ℝ) ≤ X := Nat.floor_pos.1 (by omega)
    unfold rCore
    congr 1
    ext u
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hu1, huN⟩, hcop, hN'⟩
      refine ⟨⟨⟨hu1, le_trans huN hN.2⟩, hcop, ?_⟩, hN'⟩
      rw [hN']
      exact le_trans (by exact_mod_cast hN.2) (Nat.floor_le (by linarith))
    · rintro ⟨⟨⟨hu1, _⟩, hcop, _⟩, hN'⟩
      refine ⟨⟨hu1, ?_⟩, hcop, hN'⟩
      rw [← hN']
      exact le_aliquot_core hD hu1
  · intro u hu
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hu
    obtain ⟨⟨hu1, _⟩, _, hle⟩ := hu
    rw [Finset.mem_coe, Finset.mem_Icc]
    exact ⟨le_trans hu1 (le_aliquot_core hD hu1), Nat.le_floor hle⟩

open Classical in
/-- The targets hit by some parameter lie in `𝒯_D` or come from an exceptional parameter. -/
theorem card_rCore_pos_le {D : ℕ} (_hD : D ∈ collisionCores) (X : ℝ) :
    ((Finset.Icc 1 ⌊X⌋₊).filter (fun N => 0 < rCore D N)).card ≤
      cnt {N : ℕ | D ∣ N ∧ Nat.Coprime (N / D) 30} X +
      ((Finset.Icc 1 ⌊X⌋₊).filter (fun u : ℕ => Nat.Coprime u 30 ∧ (aliquot (D * u) : ℝ) ≤ X ∧
        ¬ (D ∣ aliquot (D * u) ∧ Nat.Coprime (aliquot (D * u) / D) 30))).card := by
  set T : Set ℕ := {N : ℕ | D ∣ N ∧ Nat.Coprime (N / D) 30} with hT
  set E := (Finset.Icc 1 ⌊X⌋₊).filter (fun u : ℕ => Nat.Coprime u 30 ∧
    (aliquot (D * u) : ℝ) ≤ X ∧ ¬ (D ∣ aliquot (D * u) ∧ Nat.Coprime (aliquot (D * u) / D) 30))
    with hE
  have hsub : (Finset.Icc 1 ⌊X⌋₊).filter (fun N => 0 < rCore D N) ⊆
      (Finset.Icc 1 ⌊X⌋₊).filter (· ∈ T) ∪ E.image (fun u => aliquot (D * u)) := by
    intro N hN
    rw [Finset.mem_filter, Finset.mem_Icc] at hN
    obtain ⟨⟨hN1, hNX⟩, hpos⟩ := hN
    rw [Finset.mem_union]
    by_cases hNT : N ∈ T
    · left
      rw [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hN1, hNX⟩, hNT⟩
    · right
      unfold rCore at hpos
      obtain ⟨u, hu⟩ := Finset.card_pos.1 hpos
      rw [Finset.mem_filter, Finset.mem_Icc] at hu
      obtain ⟨⟨hu1, huN⟩, hcop, hsu⟩ := hu
      have hX1 : (1 : ℝ) ≤ X := Nat.floor_pos.1 (by omega)
      rw [Finset.mem_image]
      refine ⟨u, ?_, hsu⟩
      rw [hE, Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨hu1, le_trans huN hNX⟩, hcop, ?_, ?_⟩
      · rw [hsu]
        exact le_trans (by exact_mod_cast hNX) (Nat.floor_le (by linarith))
      · rw [hsu]
        exact hNT
  calc ((Finset.Icc 1 ⌊X⌋₊).filter (fun N => 0 < rCore D N)).card
      ≤ ((Finset.Icc 1 ⌊X⌋₊).filter (· ∈ T) ∪ E.image (fun u => aliquot (D * u))).card :=
        Finset.card_le_card hsub
    _ ≤ ((Finset.Icc 1 ⌊X⌋₊).filter (· ∈ T)).card + (E.image (fun u => aliquot (D * u))).card :=
        Finset.card_union_le _ _
    _ ≤ cnt T X + E.card := by
        have hcT : ((Finset.Icc 1 ⌊X⌋₊).filter (· ∈ T)).card = cnt T X := by
          unfold cnt
          convert rfl
        rw [hcT]
        exact Nat.add_le_add_left Finset.card_image_le _

theorem perCore_link : Principia.Erdos1054.Spine.Link_Step_DaddCollisionPerCore := by
  intro hSI hCyl D hD ε hε
  obtain ⟨WD, hWlim, _, hWge⟩ := hSI D hD
  obtain ⟨hexc, hdens⟩ := hCyl D hD
  have hTR := hasDens_tendsto_real hdens
  set T : Set ℕ := {N : ℕ | D ∣ N ∧ Nat.Coprime (N / D) 30} with hT
  have hlow := (hWlim.sub hTR).sub hexc
  rw [sub_zero] at hlow
  have hcore : coreTerm D ≤ WD - Delta 5 / D := by
    unfold coreTerm
    have : Delta 5 * (1 / ((aliquot D : ℝ) + sig D * collisionH) - 1 / (D : ℝ)) =
        Delta 5 / ((aliquot D : ℝ) + sig D * collisionH) - Delta 5 / D := by ring
    rw [this]
    linarith
  have hev := (tendsto_order.1 hlow).1 (WD - Delta 5 / D - ε) (by linarith)
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.1 (hev.and (eventually_gt_atTop (0 : ℝ)))
  refine ⟨X₀, fun X hX => ?_⟩
  obtain ⟨hlt, hXpos⟩ := hX₀ X hX
  -- the pointwise inequality `(r − 1)_+ ≥ r − 1_{r > 0}`
  have hpt : ∑ N ∈ Finset.Icc 1 ⌊X⌋₊, (rCore D N : ℝ) -
      ((((Finset.Icc 1 ⌊X⌋₊).filter (fun N => 0 < rCore D N)).card : ℕ) : ℝ) ≤
      ∑ N ∈ Finset.Icc 1 ⌊X⌋₊, ((rCore D N - 1 : ℕ) : ℝ) := by
    rw [Finset.natCast_card_filter, ← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun N _ => ?_
    rcases Nat.eq_zero_or_pos (rCore D N) with h | h
    · rw [h]
      simp
    · rw [if_pos h, Nat.cast_sub h]
      push_cast
      exact le_rfl
  have hsum := sum_rCore_eq hD X
  have hsumR : ∑ N ∈ Finset.Icc 1 ⌊X⌋₊, (rCore D N : ℝ) =
      ((((Finset.Icc 1 ⌊X⌋₊).filter (fun u : ℕ =>
          Nat.Coprime u 30 ∧ (aliquot (D * u) : ℝ) ≤ X)).card : ℕ) : ℝ) := by
    rw [← hsum]
    push_cast
    rfl
  have hpos := card_rCore_pos_le hD X
  have hposR : ((((Finset.Icc 1 ⌊X⌋₊).filter (fun N => 0 < rCore D N)).card : ℕ) : ℝ) ≤
      (cnt T X : ℝ) +
      ((((Finset.Icc 1 ⌊X⌋₊).filter (fun u : ℕ => Nat.Coprime u 30 ∧ (aliquot (D * u) : ℝ) ≤ X ∧
        ¬ (D ∣ aliquot (D * u) ∧ Nat.Coprime (aliquot (D * u) / D) 30))).card : ℕ) : ℝ) := by
    exact_mod_cast hpos
  have hXinv : 0 < 1 / X := by positivity
  have key : (1 / X) * ((((Finset.Icc 1 ⌊X⌋₊).filter (fun u : ℕ =>
          Nat.Coprime u 30 ∧ (aliquot (D * u) : ℝ) ≤ X)).card : ℕ) : ℝ) - (cnt T X : ℝ) / X -
      (1 / X) * ((((Finset.Icc 1 ⌊X⌋₊).filter (fun u : ℕ => Nat.Coprime u 30 ∧
        (aliquot (D * u) : ℝ) ≤ X ∧
        ¬ (D ∣ aliquot (D * u) ∧ Nat.Coprime (aliquot (D * u) / D) 30))).card : ℕ) : ℝ) ≤
      (1 / X) * ∑ N ∈ Finset.Icc 1 ⌊X⌋₊, ((rCore D N - 1 : ℕ) : ℝ) := by
    rw [div_eq_mul_one_div (cnt T X : ℝ) X]
    have h1 : ∑ N ∈ Finset.Icc 1 ⌊X⌋₊, (rCore D N : ℝ) - ((cnt T X : ℝ) +
        ((((Finset.Icc 1 ⌊X⌋₊).filter (fun u : ℕ => Nat.Coprime u 30 ∧
          (aliquot (D * u) : ℝ) ≤ X ∧
          ¬ (D ∣ aliquot (D * u) ∧ Nat.Coprime (aliquot (D * u) / D) 30))).card : ℕ) : ℝ)) ≤
        ∑ N ∈ Finset.Icc 1 ⌊X⌋₊, (rCore D N : ℝ) -
          ((((Finset.Icc 1 ⌊X⌋₊).filter (fun N => 0 < rCore D N)).card : ℕ) : ℝ) := by
      linarith
    have h2 := mul_le_mul_of_nonneg_left (le_trans h1 hpt) hXinv.le
    rw [hsumR] at h2
    linarith
  have hcore' : Delta 5 * (1 / ((aliquot D : ℝ) + sig D * collisionH) - 1 / (D : ℝ)) ≤
      WD - Delta 5 / D := hcore
  linarith

/-! ## The empirical first moment -/

/-- `h(u) = ∑_{d ∣ u} 1/d`. -/
theorem abundancy_eq_sum (u : ℕ) (hu : 1 ≤ u) :
    abundancy u = ∑ d ∈ u.divisors, (1 : ℝ) / d := by
  have hu0 : (u : ℝ) ≠ 0 := by exact_mod_cast (show u ≠ 0 by omega)
  rw [← Nat.sum_div_divisors u (fun d : ℕ => (1 : ℝ) / (d : ℝ)), abundancy]
  show ((ArithmeticFunction.sigma 1 u : ℕ) : ℝ) / u = _
  rw [ArithmeticFunction.sigma_one_apply, Nat.cast_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdu : d ∣ u := Nat.dvd_of_mem_divisors hd
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
  rw [Nat.cast_div hdu hd0]
  field_simp

/-- `h(u) − 1 = ∑_{2 ≤ d ≤ n, d ∣ u} 1/d` for `1 ≤ u ≤ n`. -/
theorem abundancy_sub_one_eq (u n : ℕ) (hu : 1 ≤ u) (hun : u ≤ n) :
    abundancy u - 1 = ∑ d ∈ Finset.Icc 2 n, if d ∣ u then (1 : ℝ) / d else 0 := by
  rw [abundancy_eq_sum u hu]
  have hdiv : u.divisors = (Finset.Icc 1 n).filter (· ∣ u) := by
    ext d
    simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨hd, _⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hd (by omega), le_trans (Nat.le_of_dvd (by omega) hd) hun⟩, hd⟩
    · rintro ⟨_, hd⟩
      exact ⟨hd, by omega⟩
  rw [hdiv, Finset.sum_filter]
  have hIcc : Finset.Icc 1 n = insert 1 (Finset.Icc 2 n) := by
    ext d
    simp only [Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [hIcc, Finset.sum_insert (by simp)]
  simp

/-- `#{u ≤ n : (u,30)=1, d ∣ u} = [(d,30)=1] · #{k ≤ n/d : (k,30)=1}`. -/
theorem card_cop_dvd (n d : ℕ) (hd : 1 ≤ d) :
    ((Finset.Icc 1 n).filter (fun u => Nat.Coprime u 30 ∧ d ∣ u)).card =
      if Nat.Coprime d 30 then ((Finset.Icc 1 (n / d)).filter (fun k => Nat.Coprime k 30)).card
      else 0 := by
  split_ifs with hcd
  · have himg : (Finset.Icc 1 n).filter (fun u => Nat.Coprime u 30 ∧ d ∣ u) =
        ((Finset.Icc 1 (n / d)).filter (fun k => Nat.Coprime k 30)).image (d * ·) := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
      constructor
      · rintro ⟨⟨hu1, hun⟩, hcop, k, rfl⟩
        refine ⟨k, ⟨⟨?_, ?_⟩, (Nat.coprime_mul_iff_left.1 hcop).2⟩, rfl⟩
        · rcases Nat.eq_zero_or_pos k with hk | hk
          · subst hk
            omega
          · exact hk
        · rw [Nat.le_div_iff_mul_le hd, mul_comm]
          exact hun
      · rintro ⟨k, ⟨⟨hk1, hkn⟩, hk⟩, rfl⟩
        refine ⟨⟨Nat.mul_pos hd hk1, ?_⟩, Nat.coprime_mul_iff_left.2 ⟨hcd, hk⟩, dvd_mul_right d k⟩
        calc d * k ≤ d * (n / d) := Nat.mul_le_mul_left d hkn
          _ ≤ n := Nat.mul_div_le n d
    rw [himg, Finset.card_image_of_injective _ (fun a b h => Nat.eq_of_mul_eq_mul_left hd h)]
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro u _ ⟨hcop, hdu⟩
    exact hcd (Nat.Coprime.coprime_dvd_left hdu hcop)

/-- The exchange of summations. -/
theorem sum_abundancy_eq (n : ℕ) :
    ∑ u ∈ (Finset.Icc 1 n).filter (fun u : ℕ => Nat.Coprime u 30), (abundancy u - 1) =
      ∑ d ∈ Finset.Icc 2 n, if Nat.Coprime d 30 then
        (((Finset.Icc 1 (n / d)).filter (fun k => Nat.Coprime k 30)).card : ℝ) / d else 0 := by
  have h1 : ∑ u ∈ (Finset.Icc 1 n).filter (fun u : ℕ => Nat.Coprime u 30), (abundancy u - 1) =
      ∑ u ∈ (Finset.Icc 1 n).filter (fun u : ℕ => Nat.Coprime u 30),
        ∑ d ∈ Finset.Icc 2 n, if d ∣ u then (1 : ℝ) / d else 0 := by
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [Finset.mem_filter, Finset.mem_Icc] at hu
    exact abundancy_sub_one_eq u n hu.1.1 hu.1.2
  rw [h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd1 : 1 ≤ d := by rw [Finset.mem_Icc] at hd; omega
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, Finset.filter_filter]
  have hc := card_cop_dvd n d hd1
  split_ifs with hcd
  · rw [if_pos hcd] at hc
    rw [hc]
    ring
  · rw [if_neg hcd] at hc
    rw [hc]
    simp

theorem sum_Icc_one_eq_range (f : ℕ → ℝ) (n : ℕ) :
    ∑ d ∈ Finset.Icc 1 n, f d = ∑ i ∈ Finset.range n, f (i + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

theorem cnt_cop_thirty : cnt {k : ℕ | Nat.Coprime k 30} ((30 : ℕ) : ℝ) = 8 := by
  rw [cnt_natCast]
  have h : ((Finset.Icc 1 30).filter (fun k => Nat.Coprime k 30)).card = 8 := by decide
  refine Eq.trans ?_ h
  congr 1
  ext N
  simp only [Finset.mem_filter, Set.mem_setOf_eq]

/-- `|#{k ≤ n/d : (k,30)=1} − (4/15)(n/d)| ≤ 8`. -/
theorem abs_card_cop_sub_le (n d : ℕ) :
    |(((Finset.Icc 1 (n / d)).filter (fun k => Nat.Coprime k 30)).card : ℝ) -
        4 / 15 * ((n : ℝ) / d)| ≤ 8 := by
  have hper : ∀ N, N + 30 ∈ {k : ℕ | Nat.Coprime k 30} ↔ N ∈ {k : ℕ | Nat.Coprime k 30} := by
    intro N
    simp only [Set.mem_setOf_eq]
    exact Nat.coprime_add_self_left
  have hX : (0 : ℝ) ≤ (n : ℝ) / d := by positivity
  have h := abs_cnt_sub_le_of_periodic (by norm_num : 0 < 30) hper hX
  rw [cnt_cop_thirty] at h
  have hc : cnt {k : ℕ | Nat.Coprime k 30} ((n : ℝ) / d) =
      ((Finset.Icc 1 (n / d)).filter (fun k => Nat.Coprime k 30)).card := by
    rw [← cnt_floor, Nat.floor_div_eq_div, cnt_natCast]
    congr 1
    ext N
    simp only [Finset.mem_filter, Set.mem_setOf_eq]
  rw [hc] at h
  have e : ((8 : ℕ) : ℝ) * ((n : ℝ) / d) / ((30 : ℕ) : ℝ) = 4 / 15 * ((n : ℝ) / d) := by
    push_cast
    ring
  rw [e] at h
  exact_mod_cast h

theorem firstMoment_link : Principia.Erdos1054.Spine.Link_Step_DaddCollisionFirstMoment := by
  intro hH hCores
  have hD5 : Delta 5 = 4 / 15 := hCores.2.2.2.2.2.2.2.2
  have hzc : HasSum (zc 30) (8 * Real.pi ^ 2 / 75) := hH.1
  set a : ℕ → ℝ := fun n =>
    ∑ u ∈ (Finset.Icc 1 n).filter (fun u : ℕ => Nat.Coprime u 30), (abundancy u - 1) with ha
  -- the main term
  have hmain : Tendsto (fun n : ℕ => ∑ i ∈ Finset.range (n + 1), zc 30 i - 1) atTop
      (𝓝 (8 * Real.pi ^ 2 / 75 - 1)) :=
    ((hzc.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)).sub_const 1
  -- the error term
  have hces : Tendsto (fun n : ℕ => (n⁻¹ : ℝ) * ∑ i ∈ Finset.range n, (1 : ℝ) / ((i : ℝ) + 1))
      atTop (𝓝 0) := (tendsto_one_div_add_atTop_nhds_zero_nat).cesaro
  set err : ℕ → ℝ := fun n => (1 / (n : ℝ)) * ∑ d ∈ Finset.Icc 2 n, if Nat.Coprime d 30 then
      ((((Finset.Icc 1 (n / d)).filter (fun k => Nat.Coprime k 30)).card : ℝ) -
        4 / 15 * ((n : ℝ) / d)) / d else 0 with herr
  have herr0 : Tendsto err atTop (𝓝 0) := by
    have h8 := hces.const_mul 8
    rw [mul_zero] at h8
    refine squeeze_zero_norm' ?_ h8
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    rw [herr, norm_mul, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < 1 / n)]
    have hb : ‖∑ d ∈ Finset.Icc 2 n, if Nat.Coprime d 30 then
        ((((Finset.Icc 1 (n / d)).filter (fun k => Nat.Coprime k 30)).card : ℝ) -
          4 / 15 * ((n : ℝ) / d)) / d else 0‖ ≤
        8 * ∑ i ∈ Finset.range n, (1 : ℝ) / ((i : ℝ) + 1) := by
      refine (norm_sum_le _ _).trans ?_
      have h2 : ∑ d ∈ Finset.Icc 2 n, ‖if Nat.Coprime d 30 then
          ((((Finset.Icc 1 (n / d)).filter (fun k => Nat.Coprime k 30)).card : ℝ) -
            4 / 15 * ((n : ℝ) / d)) / d else 0‖ ≤ ∑ d ∈ Finset.Icc 2 n, 8 * ((1 : ℝ) / d) := by
        refine Finset.sum_le_sum fun d hd => ?_
        have hdpos : (0 : ℝ) < d := by
          rw [Finset.mem_Icc] at hd
          exact_mod_cast (show 0 < d by omega)
        split_ifs
        · rw [Real.norm_eq_abs, abs_div, abs_of_pos hdpos, div_eq_mul_one_div]
          exact mul_le_mul_of_nonneg_right (abs_card_cop_sub_le n d) (by positivity)
        · rw [norm_zero]
          positivity
      refine h2.trans ?_
      rw [← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      have hs := sum_Icc_one_eq_range (fun d : ℕ => (1 : ℝ) / d) n
      push_cast at hs
      rw [← hs]
      · refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
        intro d hd
        rw [Finset.mem_Icc] at hd ⊢
        omega
    have e2 : (1 / (n : ℝ)) * (8 * ∑ i ∈ Finset.range n, (1 : ℝ) / ((i : ℝ) + 1)) =
        8 * ((n⁻¹ : ℝ) * ∑ i ∈ Finset.range n, (1 : ℝ) / ((i : ℝ) + 1)) := by
      rw [one_div]
      ring
    rw [← e2]
    exact mul_le_mul_of_nonneg_left hb (by positivity)
  -- the decomposition
  have hdec : ∀ n : ℕ, 1 ≤ n → a n / n =
      4 / 15 * (∑ i ∈ Finset.range (n + 1), zc 30 i - 1) + err n := by
    intro n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hr : ∑ i ∈ Finset.range (n + 1), zc 30 i - 1 = ∑ d ∈ Finset.Icc 2 n, zc 30 d := by
      rw [Finset.sum_range_succ', ← sum_Icc_one_eq_range (fun d => zc 30 d) n]
      have hIcc : Finset.Icc 1 n = insert 1 (Finset.Icc 2 n) := by
        ext d
        simp only [Finset.mem_insert, Finset.mem_Icc]
        omega
      rw [hIcc, Finset.sum_insert (by simp)]
      simp [zc]
    rw [hr]
    simp only [ha, herr]
    rw [sum_abundancy_eq n, Finset.mul_sum, Finset.mul_sum, Finset.sum_div,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hdpos : (0 : ℝ) < d := by
      rw [Finset.mem_Icc] at hd
      exact_mod_cast (show 0 < d by omega)
    unfold zc
    split_ifs
    · field_simp
      ring
    · simp
  have hlim : Tendsto (fun n : ℕ => a n / n) atTop
      (𝓝 (4 / 15 * (8 * Real.pi ^ 2 / 75 - 1) + 0)) := by
    refine ((hmain.const_mul (4 / 15)).add herr0).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact (hdec n hn).symm
  rw [add_zero] at hlim
  have hreal := tendsto_div_real_of_nat hlim
  unfold Step_DaddCollisionFirstMoment
  rw [hD5]
  unfold collisionH
  refine hreal.congr (fun X => ?_)
  simp only [ha]
  ring

/-! ## `prop:dadd:collision-criterion` -/

/-- The empirical laws as probability measures (`ν_X` for `X ≥ 1`; junk `δ_0` below). -/
noncomputable def muP (hProb : EmpiricalMeasures_isProbability) (X : ℝ) :
    ProbabilityMeasure ℝ≥0∞ :=
  if h : 1 ≤ X then ⟨nuX X, hProb X h⟩ else ⟨Measure.dirac 0, inferInstance⟩

theorem muP_coe (hProb : EmpiricalMeasures_isProbability) {X : ℝ} (hX : 1 ≤ X) :
    ((muP hProb X : ProbabilityMeasure ℝ≥0∞) : Measure ℝ≥0∞) = nuX X := by
  unfold muP
  rw [dif_pos hX]
  rfl

/-- Weak convergence of `muP` along a filter `≤ atTop` gives the integral convergence for `ν_X`. -/
theorem integral_tendsto_of_muP {ι : Type*} {F : Filter ι} (hProb : EmpiricalMeasures_isProbability)
    {Y : ι → ℝ} (hY : Tendsto Y F atTop) {μ : ProbabilityMeasure ℝ≥0∞}
    (h : Tendsto (fun i => muP hProb (Y i)) F (𝓝 μ)) (φ : ℝ≥0∞ →ᵇ ℝ) :
    Tendsto (fun i => ∫ x, φ x ∂(nuX (Y i))) F (𝓝 (∫ x, φ x ∂(μ : Measure ℝ≥0∞))) := by
  have h1 := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 h) φ
  refine h1.congr' ?_
  filter_upwards [hY.eventually (eventually_ge_atTop (1 : ℝ))] with i hi
  rw [muP_coe hProb hi]

/-- At a no-atom point `ofReal q`, weak convergence of `muP` gives `ν_X([0, q]) → ν([0, q])`. -/
theorem nuX_real_tendsto_of_muP {ι : Type*} {F : Filter ι}
    (hProb : EmpiricalMeasures_isProbability) {Y : ι → ℝ} (hY : Tendsto Y F atTop)
    {μ : ProbabilityMeasure ℝ≥0∞} (h : Tendsto (fun i => muP hProb (Y i)) F (𝓝 μ)) {q : ℝ}
    (hat : (μ : Measure ℝ≥0∞) {ENNReal.ofReal q} = 0) :
    Tendsto (fun i => (nuX (Y i)).real (Set.Iic (ENNReal.ofReal q))) F
      (𝓝 ((μ : Measure ℝ≥0∞).real (Set.Iic (ENNReal.ofReal q)))) := by
  have hfr : (μ : Measure ℝ≥0∞) (frontier (Set.Iic (ENNReal.ofReal q))) = 0 :=
    measure_mono_null (frontier_Iic_subset _) hat
  have hport := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' h hfr
  have h2 := (ENNReal.tendsto_toReal (measure_ne_top (μ : Measure ℝ≥0∞) _)).comp hport
  refine h2.congr' ?_
  filter_upwards [hY.eventually (eventually_ge_atTop (1 : ℝ))] with i hi
  simp only [Function.comp, measureReal_def, muP_coe hProb hi]

/-- Two probability measures on `[0, ∞]` with the same values on every `[0, q]`, `q ∈ ℚ_{>0}`,
coincide. -/
theorem probMeasure_eq_of_Iic_rat {μ ν : ProbabilityMeasure ℝ≥0∞}
    (h : ∀ q : ℚ, 0 < q → (μ : Measure ℝ≥0∞) (Set.Iic (ENNReal.ofReal q)) =
      (ν : Measure ℝ≥0∞) (Set.Iic (ENNReal.ofReal q))) : μ = ν := by
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext_of_Iic
  intro a
  by_cases ha : a = ⊤
  · subst ha
    rw [Set.Iic_top, measure_univ, measure_univ]
  · let ι := {q : ℚ // a < ENNReal.ofReal q}
    have hset : Set.Iic a = ⋂ i : ι, Set.Iic (ENNReal.ofReal (i : ℚ)) := by
      ext x
      simp only [Set.mem_Iic, Set.mem_iInter]
      constructor
      · intro hx i
        exact le_trans hx i.2.le
      · intro hx
        by_contra hlt0
        have hlt := not_le.1 hlt0
        obtain ⟨q, hq0, haq, hqx⟩ := ENNReal.lt_iff_exists_rat_btwn.1 hlt
        have hq' : a < ENNReal.ofReal (q : ℝ) := haq
        have := hx ⟨q, hq'⟩
        exact absurd (lt_of_le_of_lt this hqx) (lt_irrefl _)
    have hne : Nonempty ι := by
      obtain ⟨q, _, haq, _⟩ := ENNReal.lt_iff_exists_rat_btwn.1 (lt_top_iff_ne_top.2 ha)
      exact ⟨⟨q, haq⟩⟩
    have hdir : Directed (· ⊇ ·) (fun i : ι => Set.Iic (ENNReal.ofReal (i : ℚ))) := by
      intro i j
      by_cases hij : (i : ℚ) ≤ j
      · refine ⟨i, le_rfl, ?_⟩
        exact Set.Iic_subset_Iic.2 (ENNReal.ofReal_le_ofReal (by exact_mod_cast hij))
      · refine ⟨j, ?_, le_rfl⟩
        exact Set.Iic_subset_Iic.2 (ENNReal.ofReal_le_ofReal (by exact_mod_cast (le_of_not_ge hij)))
    have hpos : ∀ i : ι, 0 < (i : ℚ) := by
      intro i
      have h1 : (0 : ℝ≥0∞) < ENNReal.ofReal (i : ℚ) := lt_of_le_of_lt zero_le i.2
      have h2 : (0 : ℝ) < ((i : ℚ) : ℝ) := ENNReal.ofReal_pos.1 h1
      exact_mod_cast h2
    have hm : ∀ i : ι, NullMeasurableSet (Set.Iic (ENNReal.ofReal (i : ℚ))) (μ : Measure ℝ≥0∞) :=
      fun i => measurableSet_Iic.nullMeasurableSet
    have hm' : ∀ i : ι, NullMeasurableSet (Set.Iic (ENNReal.ofReal (i : ℚ))) (ν : Measure ℝ≥0∞) :=
      fun i => measurableSet_Iic.nullMeasurableSet
    obtain ⟨i0⟩ := hne
    rw [hset, hdir.measure_iInter hm ⟨i0, measure_ne_top _ _⟩,
      hdir.measure_iInter hm' ⟨i0, measure_ne_top _ _⟩]
    exact iInf_congr fun i => h i (hpos i)

theorem propCriterion_link : Principia.Erdos1054.Spine.Link_Prop_DaddCollisionCriterion := by
  intro hEq hRc hCar hProb
  obtain ⟨Z, -, -, -, hZ⟩ := hCar
  refine ⟨hEq, ?_, ?_⟩
  · -- the threshold density exists iff `K_X(t)` converges
    intro t ht
    have hK := hEq t ht
    have hν := tendsto_nuX_sub_cnt hRc ht.le
    constructor
    · rintro ⟨d, hd⟩
      have hc : Tendsto (fun X : ℝ => (cnt (smallRatioSet t) X : ℝ) / X) atTop (𝓝 d) :=
        hasDens_tendsto_real hd
      refine ⟨WstarFun t - d, ?_⟩
      have h1 := (tendsto_const_nhds (x := WstarFun t)).sub ((hc.add hν).sub hK)
      rw [add_zero, sub_zero] at h1
      refine h1.congr (fun X => ?_)
      ring
    · rintro ⟨L, hL⟩
      refine ⟨WstarFun t - L, hasDens_of_tendsto_real ?_⟩
      have h1 := (((tendsto_const_nhds (x := WstarFun t)).sub hL).add hK).sub hν
      rw [add_zero, sub_zero] at h1
      refine h1.congr (fun X => ?_)
      show WstarFun t - KX X t + ((nuX X).real (Set.Iic (ENNReal.ofReal t)) -
        (WstarFun t - KX X t)) - ((nuX X).real (Set.Iic (ENNReal.ofReal t)) -
          (cnt (smallRatioSet t) X : ℝ) / X) = (cnt (smallRatioSet t) X : ℝ) / X
      ring
  · constructor
    · -- weak convergence ⟹ convergence of every `K_X(q)`
      rintro ⟨ν, hνP, hconv⟩ q hq
      have hWSL : IsWeakSubseqLimit ν :=
        ⟨hνP, fun j : ℕ => (j : ℝ), tendsto_natCast_atTop_atTop,
          fun φ => (hconv φ).comp tendsto_natCast_atTop_atTop⟩
      have hq' : (0 : ℝ) < q := by exact_mod_cast hq
      have hat : ν {ENNReal.ofReal (q : ℝ)} = 0 :=
        (hZ ν hWSL).2.2.2 _ (by rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact hq')
          ENNReal.ofReal_ne_top
      let μ : ProbabilityMeasure ℝ≥0∞ := ⟨ν, hνP⟩
      have hlim : Tendsto (fun X : ℝ => muP hProb X) atTop (𝓝 μ) := by
        rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
        intro φ
        refine (hconv φ).congr' ?_
        filter_upwards [eventually_ge_atTop (1 : ℝ)] with X hX
        rw [muP_coe hProb hX]
      have hreal := nuX_real_tendsto_of_muP hProb tendsto_id hlim (q := (q : ℝ)) hat
      refine ⟨WstarFun q - ν.real (Set.Iic (ENNReal.ofReal (q : ℝ))), ?_⟩
      have h1 := ((tendsto_const_nhds (x := WstarFun q)).sub hreal).add (hEq q hq')
      rw [add_zero] at h1
      refine h1.congr (fun X => ?_)
      simp only [id]
      ring
    · -- convergence of every `K_X(q)` ⟹ weak convergence
      intro hKq
      choose! L hL using hKq
      have hnuq : ∀ q : ℚ, 0 < q → Tendsto (fun X : ℝ => (nuX X).real
          (Set.Iic (ENNReal.ofReal (q : ℝ)))) atTop (𝓝 (WstarFun q - L q)) := by
        intro q hq
        have hq' : (0 : ℝ) < q := by exact_mod_cast hq
        have h1 := (hEq q hq').add ((tendsto_const_nhds (x := WstarFun q)).sub (hL q hq))
        rw [zero_add] at h1
        refine h1.congr (fun X => ?_)
        ring
      -- every cluster point has the same values on the `[0, q]`
      have hclus : ∀ ν : ProbabilityMeasure ℝ≥0∞, MapClusterPt ν atTop (muP hProb) →
          ∀ q : ℚ, 0 < q → (ν : Measure ℝ≥0∞) (Set.Iic (ENNReal.ofReal (q : ℝ))) =
            ENNReal.ofReal (WstarFun q - L q) := by
        intro ν hν q hq
        obtain ⟨ψ, hψν, hψ⟩ := hν.exists_seq_tendsto
        have hq' : (0 : ℝ) < q := by exact_mod_cast hq
        have hWSL : IsWeakSubseqLimit (ν : Measure ℝ≥0∞) :=
          ⟨inferInstance, ψ, hψ, fun φ => integral_tendsto_of_muP hProb hψ hψν φ⟩
        have hat : (ν : Measure ℝ≥0∞) {ENNReal.ofReal (q : ℝ)} = 0 :=
          (hZ _ hWSL).2.2.2 _ (by rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact hq')
            ENNReal.ofReal_ne_top
        have h1 := nuX_real_tendsto_of_muP hProb hψ hψν hat
        have h2 := (hnuq q hq).comp hψ
        have heq := tendsto_nhds_unique h1 h2
        rw [← heq, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
      obtain ⟨ν0, hν0⟩ := exists_clusterPt_of_compactSpace (map (muP hProb) atTop)
      have huniq : ∀ ν : ProbabilityMeasure ℝ≥0∞, MapClusterPt ν atTop (muP hProb) → ν = ν0 := by
        intro ν hν
        apply probMeasure_eq_of_Iic_rat
        intro q hq
        rw [hclus ν hν q hq, hclus ν0 hν0 q hq]
      have hlim := tendsto_nhds_of_unique_mapClusterPt huniq
      exact ⟨(ν0 : Measure ℝ≥0∞), inferInstance,
        fun φ => integral_tendsto_of_muP hProb tendsto_id hlim φ⟩

/-! ## The law `ν_Q` and its first moment -/

theorem lcmUpTo_five : lcmUpTo 5 = 60 := by
  unfold lcmUpTo
  rw [show ⌊(5 : ℝ)⌋₊ = 5 from Nat.floor_ofNat 5]
  decide

theorem lcmUpTo_five' : lcmUpTo ((5 : ℕ) : ℝ) = 60 := by
  rw [Nat.cast_ofNat]
  exact lcmUpTo_five

/-- The sixteen reduced classes modulo `60`. -/
def classesQ : Finset ℕ := (Finset.range 60).filter (fun a : ℕ => Nat.Coprime a 30)

theorem card_classesQ : classesQ.card = 16 := by decide

theorem nuQ_eq : nuQ = ∑ a ∈ classesQ, progLaw 5 a := by
  unfold nuQ classesQ
  rw [lcmUpTo_five]

theorem one_le_abundancy {n : ℕ} (hn : 1 ≤ n) : 1 ≤ abundancy n := by
  unfold abundancy
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [le_div_iff₀ hn', one_mul]
  exact_mod_cast sig_ge n

theorem abundancy_nonneg (n : ℕ) : 0 ≤ abundancy n := by
  unfold abundancy
  positivity

theorem cop_mod60 (n : ℕ) : Nat.Coprime (n % 60) 30 ↔ Nat.Coprime n 30 := by
  have h : n = n % 60 + 30 * (2 * (n / 60)) := by omega
  conv_rhs => rw [h]
  exact (Nat.coprime_add_mul_left_left _ _ _).symm

theorem mem_classesQ_mod {n : ℕ} : n % 60 ∈ classesQ ↔ Nat.Coprime n 30 := by
  unfold classesQ
  rw [Finset.mem_filter, Finset.mem_range, cop_mod60]
  exact ⟨fun h => h.2, fun h => ⟨Nat.mod_lt n (by norm_num), h⟩⟩

theorem progLaw_finite (hPL : Fact_DaddProgressionLaws) (a : ℕ) :
    IsFiniteMeasure (progLaw 5 a) := (hPL 5 (by norm_num) a).1.1

theorem nuQ_univ (hPL : Fact_DaddProgressionLaws) : nuQ Set.univ = ENNReal.ofReal (4 / 15) := by
  rw [nuQ_eq, Measure.finsetSum_apply]
  have h1 : ∀ a ∈ classesQ, progLaw 5 a Set.univ = (60 : ℝ≥0∞)⁻¹ := by
    intro a _
    rw [(hPL 5 (by norm_num) a).2.2.2.1, lcmUpTo_five']
    norm_num
  rw [Finset.sum_congr rfl h1, Finset.sum_const, card_classesQ, nsmul_eq_mul,
    show (4 / 15 : ℝ) = 16 / 60 by norm_num, ENNReal.ofReal_div_of_pos (by norm_num),
    ENNReal.ofReal_ofNat, ENNReal.ofReal_ofNat, div_eq_mul_inv]
  norm_num

theorem nuQ_finite (hPL : Fact_DaddProgressionLaws) : IsFiniteMeasure nuQ :=
  ⟨by rw [nuQ_univ hPL]; exact ENNReal.ofReal_lt_top⟩

theorem nuQ_real_univ (hPL : Fact_DaddProgressionLaws) : nuQ.real Set.univ = 4 / 15 := by
  rw [measureReal_def, nuQ_univ hPL, ENNReal.toReal_ofReal (by norm_num)]

open Classical in
/-- Counting a set class by class modulo `Q`. -/
theorem cnt_split_mod {A : Finset ℕ} {Q : ℕ} {C : ℕ → Prop} (hA : ∀ n, n % Q ∈ A ↔ C n)
    (P : ℕ → Prop) (X : ℝ) :
    cnt {n : ℕ | C n ∧ P n} X = ∑ a ∈ A, cnt {n : ℕ | n % Q = a ∧ P n} X := by
  unfold cnt
  rw [Finset.card_eq_sum_card_fiberwise (f := fun n => n % Q) (t := A)]
  · refine Finset.sum_congr rfl fun a ha => ?_
    congr 1
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, Set.mem_setOf_eq]
    constructor
    · rintro ⟨⟨hn, _, hP⟩, hna⟩
      exact ⟨hn, hna, hP⟩
    · rintro ⟨hn, hna, hP⟩
      refine ⟨⟨hn, ?_, hP⟩, hna⟩
      rw [← hA, hna]
      exact ha
  · intro n hn
    simp only [Finset.mem_coe, Finset.mem_filter, Set.mem_setOf_eq] at hn
    rw [Finset.mem_coe, hA]
    exact hn.2.1

theorem cnt_cop_split (P : ℕ → Prop) (X : ℝ) :
    (cnt {n : ℕ | Nat.Coprime n 30 ∧ P n} X : ℝ) =
      ∑ a ∈ classesQ, (cnt {n : ℕ | n % 60 = a ∧ P n} X : ℝ) := by
  rw [cnt_split_mod (A := classesQ) (Q := 60) (fun n => mem_classesQ_mod) P X]
  push_cast
  rfl

/-- The distribution function of `ν_Q`. -/
theorem hasDens_nuQ_Iic (hPL : Fact_DaddProgressionLaws) (u : ℝ) :
    HasDens {n : ℕ | Nat.Coprime n 30 ∧ abundancy n ≤ u} (nuQ.real (Set.Iic u)) := by
  have hparts : ∀ a ∈ classesQ,
      HasDens {n : ℕ | n % 60 = a ∧ abundancy n ≤ u} ((progLaw 5 a).real (Set.Iic u)) := by
    intro a ha
    have ha60 : a < 60 := by
      unfold classesQ at ha
      rw [Finset.mem_filter, Finset.mem_range] at ha
      exact ha.1
    have h := (hPL 5 (by norm_num) a).1.2 u
    rw [lcmUpTo_five', Nat.mod_eq_of_lt ha60] at h
    exact h
  have hreal : nuQ.real (Set.Iic u) = ∑ a ∈ classesQ, (progLaw 5 a).real (Set.Iic u) := by
    rw [nuQ_eq, measureReal_def, Measure.finsetSum_apply, ENNReal.toReal_sum]
    · rfl
    · intro a _
      haveI := progLaw_finite hPL a
      exact measure_ne_top _ _
  unfold HasDens
  rw [hreal]
  have := tendsto_finsetSum classesQ (fun a ha => hparts a ha)
  refine this.congr (fun n => ?_)
  rw [cnt_cop_split (fun n => abundancy n ≤ u), Finset.sum_div]

theorem hasDens_cop : HasDens {n : ℕ | Nat.Coprime n 30} (4 / 15) := by
  have hper : ∀ N, N + 30 ∈ {k : ℕ | Nat.Coprime k 30} ↔ N ∈ {k : ℕ | Nat.Coprime k 30} := by
    intro N
    simp only [Set.mem_setOf_eq]
    exact Nat.coprime_add_self_left
  have h := hasDens_of_periodic (by norm_num : 0 < 30) hper
  rw [cnt_cop_thirty] at h
  convert h using 1
  norm_num

open Classical in
theorem cnt_split_le (S : Set ℕ) (P : ℕ → Prop) (X : ℝ) :
    cnt {n : ℕ | n ∈ S ∧ P n} X + cnt {n : ℕ | n ∈ S ∧ ¬ P n} X = cnt S X := by
  unfold cnt
  rw [← Finset.card_filter_add_card_filter_not (s := (Finset.Icc 1 ⌊X⌋₊).filter (· ∈ S))
    (p := P)]
  congr 1
  · congr 1
    ext n
    simp only [Finset.mem_filter, Set.mem_setOf_eq, and_assoc]
  · congr 1
    ext n
    simp only [Finset.mem_filter, Set.mem_setOf_eq, and_assoc]

/-- The tail function of `ν_Q`. -/
theorem hasDens_nuQ_Ioi (hPL : Fact_DaddProgressionLaws) (v : ℝ) :
    HasDens {n : ℕ | Nat.Coprime n 30 ∧ v < abundancy n} (nuQ.real (Set.Ioi v)) := by
  haveI := nuQ_finite hPL
  have h1 := hasDens_nuQ_Iic hPL v
  have h2 := hasDens_cop
  have hval : nuQ.real (Set.Ioi v) = 4 / 15 - nuQ.real (Set.Iic v) := by
    rw [← Set.compl_Iic, measureReal_compl measurableSet_Iic, nuQ_real_univ hPL]
  unfold HasDens at h1 h2 ⊢
  rw [hval]
  refine (h2.sub h1).congr (fun n => ?_)
  have hs := cnt_split_le {k : ℕ | Nat.Coprime k 30} (fun k => abundancy k ≤ v) (n : ℝ)
  have e2 : {k : ℕ | k ∈ {k : ℕ | Nat.Coprime k 30} ∧ ¬ abundancy k ≤ v} =
      {k : ℕ | Nat.Coprime k 30 ∧ v < abundancy k} := by
    ext k
    simp only [Set.mem_setOf_eq, not_le]
  rw [e2] at hs
  have hs' : (cnt {k : ℕ | k ∈ {k : ℕ | Nat.Coprime k 30} ∧ abundancy k ≤ v} (n : ℝ) : ℝ) +
      (cnt {k : ℕ | Nat.Coprime k 30 ∧ v < abundancy k} (n : ℝ) : ℝ) =
      (cnt {k : ℕ | Nat.Coprime k 30} (n : ℝ) : ℝ) := by exact_mod_cast hs
  have e1 : {k : ℕ | k ∈ {k : ℕ | Nat.Coprime k 30} ∧ abundancy k ≤ v} =
      {k : ℕ | Nat.Coprime k 30 ∧ abundancy k ≤ v} := rfl
  rw [e1] at hs'
  rw [← hs']
  ring

/-- `ν_Q` gives no mass to `(−∞, 1)` (every `h(n) ≥ 1`). -/
theorem nuQ_Iio_one (hPL : Fact_DaddProgressionLaws) : nuQ (Set.Iio 1) = 0 := by
  haveI := nuQ_finite hPL
  have hIic : ∀ u : ℝ, u < 1 → nuQ (Set.Iic u) = 0 := by
    intro u hu
    have h1 := hasDens_nuQ_Iic hPL u
    have hempty : ∀ X : ℕ, cnt {n : ℕ | Nat.Coprime n 30 ∧ abundancy n ≤ u} (X : ℝ) = 0 := by
      intro X
      unfold cnt
      refine Finset.card_eq_zero.2 (Finset.eq_empty_of_forall_notMem fun n hn => ?_)
      rw [mem_cntFinset] at hn
      obtain ⟨⟨hn1, _⟩, hmem⟩ := hn
      have h1n := one_le_abundancy hn1
      have h2n : abundancy n ≤ u := hmem.2
      linarith
    have h0 : HasDens {n : ℕ | Nat.Coprime n 30 ∧ abundancy n ≤ u} 0 := by
      unfold HasDens
      simp only [hempty, Nat.cast_zero, zero_div]
      exact tendsto_const_nhds
    have := HasDens.unique h1 h0
    rwa [measureReal_eq_zero_iff] at this
  have hU : Set.Iio (1 : ℝ) = ⋃ k : ℕ, Set.Iic (1 - 1 / ((k : ℝ) + 1)) := by
    ext x
    simp only [Set.mem_Iio, Set.mem_iUnion, Set.mem_Iic]
    constructor
    · intro hx
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.2 hx)
      exact ⟨k, by linarith⟩
    · rintro ⟨k, hk⟩
      have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      linarith
  rw [hU]
  refine measure_iUnion_null fun k => hIic _ ?_
  have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
  linarith

theorem ae_one_le_nuQ (hPL : Fact_DaddProgressionLaws) : ∀ᵐ h ∂nuQ, (1 : ℝ) ≤ h := by
  rw [ae_iff]
  have : {a : ℝ | ¬ 1 ≤ a} = Set.Iio 1 := by
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_Iio, not_le]
  rw [this]
  exact nuQ_Iio_one hPL

/-- `∑_{n ≤ X} h(n)³ ≪ X` (`lem:kovac-moment` at `q = 3`, its `j = 0` term). -/
theorem kovac_cube (hKov : Lem_KovacMoment) (hNot : Notation_sigmaPrefix_zero) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ X : ℝ, 1 ≤ X → ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, abundancy n ^ 3 ≤ K * X := by
  obtain ⟨C, _, K, hK⟩ := hKov
  refine ⟨max (K * Real.exp (C * ((3 : ℕ) : ℝ) * Real.log (Real.log ((3 : ℕ) : ℝ)))) 0,
    le_max_right _ _, fun X hX => ?_⟩
  have h1 := hK 3 le_rfl X hX
  have h2 : ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, abundancy n ^ 3 ≤
      ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, S4a.prefixMoment 3 n := by
    apply Finset.sum_le_sum
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.1 hn).1
    unfold S4a.prefixMoment
    have h0 : 0 ∈ Finset.range n.divisors.card :=
      Finset.mem_range.2 (Finset.card_pos.2 ⟨n, Nat.mem_divisors_self n (by omega)⟩)
    have hle := Finset.single_le_sum (f := fun j => ((sigmaPrefix j n : ℝ) / n) ^ 3)
      (fun j _ => by positivity) h0
    have e : ((sigmaPrefix 0 n : ℝ) / n) ^ 3 = abundancy n ^ 3 := by
      rw [hNot n hn1]
      rfl
    rw [← e]
    exact hle
  have h3 : K * Real.exp (C * ((3 : ℕ) : ℝ) * Real.log (Real.log ((3 : ℕ) : ℝ))) * X ≤
      max (K * Real.exp (C * ((3 : ℕ) : ℝ) * Real.log (Real.log ((3 : ℕ) : ℝ)))) 0 * X :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)
  linarith

/-- Markov: `#{u ≤ X : (u,30)=1, h(u) − 1 > s} (1+s)³ ≤ ∑_{n ≤ X} h(n)³`. -/
theorem card_tail_mul_le (s : ℝ) (hs : 0 ≤ s) (X : ℝ) :
    ((((Finset.Icc 1 ⌊X⌋₊).filter (fun u : ℕ => Nat.Coprime u 30 ∧ s < abundancy u - 1)).card :
      ℕ) : ℝ) * (1 + s) ^ 3 ≤ ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, abundancy n ^ 3 := by
  have hpos : (0 : ℝ) < 1 + s := by linarith
  rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_mul]
  calc ∑ u ∈ (Finset.Icc 1 ⌊X⌋₊).filter (fun u : ℕ => Nat.Coprime u 30 ∧ s < abundancy u - 1),
        ((1 : ℕ) : ℝ) * (1 + s) ^ 3
      ≤ ∑ u ∈ (Finset.Icc 1 ⌊X⌋₊).filter (fun u : ℕ => Nat.Coprime u 30 ∧ s < abundancy u - 1),
          abundancy u ^ 3 := by
        apply Finset.sum_le_sum
        intro u hu
        rw [Finset.mem_filter] at hu
        rw [Nat.cast_one, one_mul]
        exact pow_le_pow_left₀ hpos.le (by linarith [hu.2.2]) 3
    _ ≤ ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, abundancy n ^ 3 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun n _ _ => pow_nonneg (abundancy_nonneg n) 3)

/-- The empirical tail function `s ↦ X⁻¹ #{u ≤ X : (u,30)=1, h(u) − 1 > s}`, as a sum of
indicators. -/
noncomputable def gX (X s : ℝ) : ℝ :=
  (1 / X) * ∑ u ∈ (Finset.Icc 1 ⌊X⌋₊).filter (fun u : ℕ => Nat.Coprime u 30),
    (Set.Iio (abundancy u - 1)).indicator (1 : ℝ → ℝ) s

theorem gX_eq_card (X s : ℝ) : gX X s = (1 / X) *
    ((((Finset.Icc 1 ⌊X⌋₊).filter (fun u : ℕ => Nat.Coprime u 30 ∧ s < abundancy u - 1)).card :
      ℕ) : ℝ) := by
  unfold gX
  congr 1
  rw [Finset.natCast_card_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun u _ => ?_
  by_cases hc : Nat.Coprime u 30 <;> by_cases hs : s < abundancy u - 1 <;>
    simp [hc, hs, Set.indicator]

theorem gX_measurable (X : ℝ) : Measurable (gX X) := by
  unfold gX
  refine Measurable.const_mul ?_ _
  refine Finset.measurable_sum _ fun u _ => ?_
  exact measurable_const.indicator measurableSet_Iio

theorem integral_gX (X : ℝ) : ∫ s in Set.Ioi 0, gX X s =
    (1 / X) * ∑ u ∈ (Finset.Icc 1 ⌊X⌋₊).filter (fun u : ℕ => Nat.Coprime u 30),
      (abundancy u - 1) := by
  unfold gX
  rw [integral_const_mul, integral_finsetSum]
  · congr 1
    refine Finset.sum_congr rfl fun u hu => ?_
    have hu1 : 1 ≤ u := (Finset.mem_Icc.1 (Finset.mem_filter.1 hu).1).1
    have hc : 0 ≤ abundancy u - 1 := by linarith [one_le_abundancy hu1]
    rw [integral_indicator_one measurableSet_Iio, measureReal_restrict_apply measurableSet_Iio,
      Set.inter_comm, Set.Ioi_inter_Iio, Real.volume_real_Ioo_of_le hc, sub_zero]
  · intro u _
    rw [integrable_indicator_iff measurableSet_Iio]
    refine integrableOn_const ?_
    rw [Measure.restrict_apply measurableSet_Iio, Set.inter_comm, Set.Ioi_inter_Iio,
      Real.volume_Ioo]
    exact ENNReal.ofReal_ne_top

theorem card_tail_eq_cnt (s X : ℝ) :
    ((Finset.Icc 1 ⌊X⌋₊).filter (fun u : ℕ => Nat.Coprime u 30 ∧ s < abundancy u - 1)).card =
      cnt {n : ℕ | Nat.Coprime n 30 ∧ 1 + s < abundancy n} X := by
  unfold cnt
  congr 1
  ext n
  simp only [Finset.mem_filter, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, by linarith⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, by linarith⟩

/-- Pointwise convergence of the empirical tail function. -/
theorem gX_tendsto (hPL : Fact_DaddProgressionLaws) (s : ℝ) :
    Tendsto (fun X : ℝ => gX X s) atTop (𝓝 (nuQ.real (Set.Ioi (1 + s)))) := by
  have h := hasDens_tendsto_real (hasDens_nuQ_Ioi hPL (1 + s))
  refine h.congr (fun X => ?_)
  rw [gX_eq_card, card_tail_eq_cnt]
  ring

/-- The uniform bound `g_X(s) ≤ K (1 + s²)⁻¹` for `X ≥ 1`, `s ≥ 0`. -/
theorem gX_le {K : ℝ} (_hK0 : 0 ≤ K)
    (hK : ∀ X : ℝ, 1 ≤ X → ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, abundancy n ^ 3 ≤ K * X)
    {X s : ℝ} (hX : 1 ≤ X) (hs : 0 ≤ s) : gX X s ≤ K * (1 + s ^ 2)⁻¹ := by
  have hXpos : (0 : ℝ) < X := by linarith
  have hm := card_tail_mul_le s hs X
  have hk := hK X hX
  rw [gX_eq_card]
  set c := ((((Finset.Icc 1 ⌊X⌋₊).filter (fun u : ℕ => Nat.Coprime u 30 ∧
    s < abundancy u - 1)).card : ℕ) : ℝ) with hc
  have hc0 : 0 ≤ c := Nat.cast_nonneg _
  have hcube : 1 + s ^ 2 ≤ (1 + s) ^ 3 := by nlinarith [sq_nonneg s, pow_nonneg hs 3]
  have h1 : c * (1 + s ^ 2) ≤ K * X := by
    calc c * (1 + s ^ 2) ≤ c * (1 + s) ^ 3 := mul_le_mul_of_nonneg_left hcube hc0
      _ ≤ K * X := le_trans hm hk
  have hpos2 : (0 : ℝ) < 1 + s ^ 2 := by positivity
  rw [le_mul_inv_iff₀ hpos2, div_mul_eq_mul_div, one_mul, div_mul_eq_mul_div,
    div_le_iff₀ hXpos]
  linarith

theorem gX_nonneg (X s : ℝ) (hX : 0 ≤ X) : 0 ≤ gX X s := by
  rw [gX_eq_card]
  positivity

/-- The tail of `ν_Q` obeys the same bound. -/
theorem nuQ_tail_le (hPL : Fact_DaddProgressionLaws) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ X : ℝ, 1 ≤ X → ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, abundancy n ^ 3 ≤ K * X)
    {s : ℝ} (hs : 0 ≤ s) : nuQ.real (Set.Ioi (1 + s)) ≤ K * (1 + s ^ 2)⁻¹ := by
  refine le_of_tendsto (gX_tendsto hPL s) ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with X hX
  exact gX_le hK0 hK hX hs

theorem integrable_nuQ (hPL : Fact_DaddProgressionLaws) (hKov : Lem_KovacMoment)
    (hNot : Notation_sigmaPrefix_zero) : Integrable (fun h : ℝ => h - 1) nuQ := by
  haveI := nuQ_finite hPL
  obtain ⟨K, hK0, hK⟩ := kovac_cube hKov hNot
  have hnn : 0 ≤ᵐ[nuQ] (fun h : ℝ => h - 1) := by
    filter_upwards [ae_one_le_nuQ hPL] with h hh
    simp only [Pi.zero_apply]
    linarith
  refine ⟨(measurable_id.sub_const 1).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal hnn,
    lintegral_eq_lintegral_meas_lt nuQ hnn (measurable_id.sub_const 1).aemeasurable]
  have hint : Integrable (fun t : ℝ => K * (1 + t ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul K
  calc ∫⁻ t in Set.Ioi 0, nuQ {a : ℝ | t < a - 1}
      ≤ ∫⁻ t in Set.Ioi 0, ENNReal.ofReal (K * (1 + t ^ 2)⁻¹) := by
        refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
        have hset : {a : ℝ | t < a - 1} = Set.Ioi (1 + t) := by
          ext a
          simp only [Set.mem_setOf_eq, Set.mem_Ioi]
          constructor <;> intro h <;> linarith
        rw [hset, ← ENNReal.ofReal_toReal (measure_ne_top nuQ (Set.Ioi (1 + t)))]
        exact ENNReal.ofReal_le_ofReal (nuQ_tail_le hPL hK0 hK (le_of_lt ht))
    _ < ⊤ := (hint.integrableOn (s := Set.Ioi 0)).lintegral_lt_top

theorem integral_nuQ_eq (hPL : Fact_DaddProgressionLaws) (hFM : Step_DaddCollisionFirstMoment)
    (hKov : Lem_KovacMoment) (hNot : Notation_sigmaPrefix_zero) :
    ∫ h, (h - 1) ∂nuQ = Delta 5 * collisionH := by
  haveI := nuQ_finite hPL
  obtain ⟨K, hK0, hK⟩ := kovac_cube hKov hNot
  have hnn : 0 ≤ᵐ[nuQ] (fun h : ℝ => h - 1) := by
    filter_upwards [ae_one_le_nuQ hPL] with h hh
    simp only [Pi.zero_apply]
    linarith
  have hlayer := (integrable_nuQ hPL hKov hNot).integral_eq_integral_meas_lt hnn
  have hset : ∀ t : ℝ, {a : ℝ | t < a - 1} = Set.Ioi (1 + t) := by
    intro t
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_Ioi]
    constructor <;> intro h <;> linarith
  simp only [hset] at hlayer
  have hDCT : Tendsto (fun X : ℝ => ∫ s in Set.Ioi 0, gX X s) atTop
      (𝓝 (∫ s in Set.Ioi 0, nuQ.real (Set.Ioi (1 + s)))) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun s => K * (1 + s ^ 2)⁻¹)
      (Eventually.of_forall fun X => (gX_measurable X).aestronglyMeasurable) ?_
      ((integrable_inv_one_add_sq.const_mul K).integrableOn)
      (Eventually.of_forall fun s => gX_tendsto hPL s)
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with X hX
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun s hs => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (gX_nonneg X s (by linarith))]
    exact gX_le hK0 hK hX (le_of_lt hs)
  have hFM' : Tendsto (fun X : ℝ => ∫ s in Set.Ioi 0, gX X s) atTop (𝓝 (Delta 5 * collisionH)) :=
    hFM.congr (fun X => (integral_gX X).symm)
  rw [hlayer]
  exact tendsto_nhds_unique hDCT hFM'

theorem firstMomentLaw_link : Principia.Erdos1054.Spine.Link_Step_DaddCollisionFirstMomentLaw := by
  intro hPL hCores hFM hKov hNot
  have hD5 : Delta 5 = 4 / 15 := hCores.2.2.2.2.2.2.2.2
  refine ⟨?_, integrable_nuQ hPL hKov hNot, ?_⟩
  · rw [nuQ_univ hPL, hD5]
  · rw [integral_nuQ_eq hPL hFM hKov hNot, hD5]
    field_simp

/-! ## The source intensity: the radial partition argument and Jensen -/

/-- `max 0 (min 1 y)`. -/
noncomputable def clamp01 (y : ℝ) : ℝ := max 0 (min 1 y)

theorem clamp01_nonneg (y : ℝ) : 0 ≤ clamp01 y := le_max_left _ _

theorem clamp01_le_one (y : ℝ) : clamp01 y ≤ 1 := max_le zero_le_one (min_le_left _ _)

theorem clamp01_of_one_le {y : ℝ} (h : 1 ≤ y) : clamp01 y = 1 := by
  unfold clamp01
  rw [min_eq_left h, max_eq_right zero_le_one]

theorem clamp01_of_nonpos {y : ℝ} (h : y ≤ 0) : clamp01 y = 0 := by
  unfold clamp01
  rw [min_eq_right (le_trans h zero_le_one), max_eq_left h]

theorem continuous_clamp01 : Continuous clamp01 :=
  continuous_const.max (continuous_const.min continuous_id)

/-- A clamped continuous function as a bounded continuous function on `ℝ × ℝ`. -/
noncomputable def clampBCF (F : ℝ × ℝ → ℝ) (hF : Continuous F) : ℝ × ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound ⟨fun p => clamp01 (F p), continuous_clamp01.comp hF⟩ 1
    (by
      intro p q
      simp only [ContinuousMap.coe_mk]
      rw [Real.dist_eq, abs_le]
      have h1 := clamp01_nonneg (F p)
      have h2 := clamp01_le_one (F p)
      have h3 := clamp01_nonneg (F q)
      have h4 := clamp01_le_one (F q)
      constructor <;> linarith)

theorem clampBCF_apply (F : ℝ × ℝ → ℝ) (hF : Continuous F) (p : ℝ × ℝ) :
    clampBCF F hF p = clamp01 (F p) := rfl

/-- `∫_{[0,1]} clamp((1 + δ − x g)/δ) dx ≤ (1 + δ)/g` for `g ≥ 1`. -/
theorem inner_upper {g δ : ℝ} (hg : 1 ≤ g) (hδ : 0 < δ) :
    ∫ x in Set.Icc (0 : ℝ) 1, clamp01 ((1 + δ - x * g) / δ) ≤ (1 + δ) / g := by
  have hgpos : 0 < g := by linarith
  set c := (1 + δ) / g with hc
  have hc0 : 0 ≤ c := by positivity
  have hint1 : IntegrableOn (fun x : ℝ => clamp01 ((1 + δ - x * g) / δ)) (Set.Icc 0 1) :=
    (continuous_clamp01.comp (by fun_prop)).integrableOn_Icc
  have hint2 : Integrable ((Set.Iic c).indicator (1 : ℝ → ℝ)) (volume.restrict (Set.Icc 0 1)) := by
    rw [integrable_indicator_iff measurableSet_Iic]
    refine integrableOn_const ?_
    rw [Measure.restrict_apply measurableSet_Iic]
    exact measure_ne_top_of_subset Set.inter_subset_right (by
      rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  calc ∫ x in Set.Icc (0 : ℝ) 1, clamp01 ((1 + δ - x * g) / δ)
      ≤ ∫ x in Set.Icc (0 : ℝ) 1, (Set.Iic c).indicator (1 : ℝ → ℝ) x := by
        refine integral_mono hint1 hint2 fun x => ?_
        by_cases hx : x ≤ c
        · rw [Set.indicator_of_mem (Set.mem_Iic.2 hx)]
          exact clamp01_le_one _
        · rw [Set.indicator_of_notMem (fun h => hx (Set.mem_Iic.1 h))]
          have hxc : c < x := not_le.1 hx
          have : 1 + δ < x * g := by
            rw [hc, div_lt_iff₀ hgpos] at hxc
            exact hxc
          rw [clamp01_of_nonpos]
          exact div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le
    _ = volume.real (Set.Iic c ∩ Set.Icc 0 1) := by
        rw [integral_indicator_one measurableSet_Iic, measureReal_restrict_apply measurableSet_Iic]
    _ ≤ volume.real (Set.Icc 0 c) := by
        refine measureReal_mono ?_ (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
        intro x hx
        exact ⟨hx.2.1, hx.1⟩
    _ = c := by rw [Real.volume_real_Icc_of_le hc0, sub_zero]

/-- `(1 − δ)/g ≤ ∫_{[0,1]} clamp((1 − x g)/δ) dx` for `g ≥ 1`, `0 < δ < 1`. -/
theorem inner_lower {g δ : ℝ} (hg : 1 ≤ g) (hδ : 0 < δ) (hδ1 : δ < 1) :
    (1 - δ) / g ≤ ∫ x in Set.Icc (0 : ℝ) 1, clamp01 ((1 - x * g) / δ) := by
  have hgpos : 0 < g := by linarith
  set c := (1 - δ) / g with hc
  have hc0 : 0 ≤ c := div_nonneg (by linarith) hgpos.le
  have hc1 : c ≤ 1 := by
    rw [hc, div_le_one hgpos]
    linarith
  have hint1 : IntegrableOn (fun x : ℝ => clamp01 ((1 - x * g) / δ)) (Set.Icc 0 1) :=
    (continuous_clamp01.comp (by fun_prop)).integrableOn_Icc
  have hint2 : Integrable ((Set.Iic c).indicator (1 : ℝ → ℝ)) (volume.restrict (Set.Icc 0 1)) := by
    rw [integrable_indicator_iff measurableSet_Iic]
    refine integrableOn_const ?_
    rw [Measure.restrict_apply measurableSet_Iic]
    exact measure_ne_top_of_subset Set.inter_subset_right (by
      rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  have hset : Set.Iic c ∩ Set.Icc 0 1 = Set.Icc 0 c := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
    constructor
    · rintro ⟨h1, h2, _⟩
      exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h2, h1, le_trans h2 hc1⟩
  calc (1 - δ) / g = volume.real (Set.Iic c ∩ Set.Icc 0 1) := by
        rw [hset, Real.volume_real_Icc_of_le hc0, sub_zero]
    _ = ∫ x in Set.Icc (0 : ℝ) 1, (Set.Iic c).indicator (1 : ℝ → ℝ) x := by
        rw [integral_indicator_one measurableSet_Iic, measureReal_restrict_apply measurableSet_Iic]
    _ ≤ ∫ x in Set.Icc (0 : ℝ) 1, clamp01 ((1 - x * g) / δ) := by
        refine integral_mono hint2 hint1 fun x => ?_
        by_cases hx : x ≤ c
        · rw [Set.indicator_of_mem (Set.mem_Iic.2 hx), Pi.one_apply]
          have : x * g ≤ 1 - δ := by
            rw [hc, le_div_iff₀ hgpos] at hx
            exact hx
          rw [clamp01_of_one_le]
          rw [le_div_iff₀ hδ]
          linarith
        · rw [Set.indicator_of_notMem (fun h => hx (Set.mem_Iic.1 h))]
          exact clamp01_nonneg _

/-- The radial partition argument for one finite law `μ` carried by `[1, ∞)`: if the joint
empirical measures converge to `1_{[0,1]}(x) dx dμ(h)`, then the proportion of sources with
`(n/X) g(h(n)) ≤ 1` tends to `∫ dμ/g`, where `g(h) = s + σ(h − 1)`. -/
theorem radial_limit {μ : Measure ℝ} [IsFiniteMeasure μ] (hsupp : μ (Set.Iio 1) = 0)
    {s σ : ℝ} (hs : 1 ≤ s) (hσ : 0 ≤ σ) {P : ℝ → Finset ℕ}
    (hJ : ∀ φ : ℝ × ℝ →ᵇ ℝ, Tendsto (fun X : ℝ => (1 / X) * ∑ n ∈ P X, φ ((n : ℝ) / X, abundancy n))
      atTop (𝓝 (∫ p, φ p ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod μ)))) :
    Tendsto (fun X : ℝ => (1 / X) *
        ((((P X).filter (fun n : ℕ => (n : ℝ) / X * (s + σ * (abundancy n - 1)) ≤ 1)).card : ℕ) : ℝ))
      atTop (𝓝 (∫ h, 1 / (s + σ * (h - 1)) ∂μ)) := by
  have hae : ∀ᵐ h ∂μ, 1 ≤ s + σ * (h - 1) := by
    have h1 : ∀ᵐ h ∂μ, (1 : ℝ) ≤ h := by
      rw [ae_iff]
      have : {a : ℝ | ¬ 1 ≤ a} = Set.Iio 1 := by
        ext a
        simp only [Set.mem_setOf_eq, Set.mem_Iio, not_le]
      rw [this]
      exact hsupp
    filter_upwards [h1] with h hh
    nlinarith
  have hmeas : Measurable (fun h : ℝ => 1 / (s + σ * (h - 1))) := by fun_prop
  have hWint : Integrable (fun h : ℝ => 1 / (s + σ * (h - 1))) μ := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) hmeas.aestronglyMeasurable ?_
    filter_upwards [hae] with h hh
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [div_le_one (by linarith)]
    exact hh
  set W := ∫ h, 1 / (s + σ * (h - 1)) ∂μ with hW
  have hW0 : 0 ≤ W := by
    refine integral_nonneg_of_ae ?_
    filter_upwards [hae] with h hh
    simp only [Pi.zero_apply]
    positivity
  -- the two test functions
  let G : ℝ × ℝ → ℝ := fun p => p.1 * (s + σ * (p.2 - 1))
  have hG : Continuous G := by fun_prop
  have hFp : ∀ δ : ℝ, Continuous (fun p : ℝ × ℝ => (1 + δ - G p) / δ) := fun δ => by fun_prop
  have hFm : ∀ δ : ℝ, Continuous (fun p : ℝ × ℝ => (1 - G p) / δ) := fun δ => by fun_prop
  -- the empirical count as a sum of indicators
  have hcount : ∀ X : ℝ, ((((P X).filter (fun n : ℕ => (n : ℝ) / X * (s + σ * (abundancy n - 1)) ≤ 1)).card
      : ℕ) : ℝ) = ∑ n ∈ P X, (if G ((n : ℝ) / X, abundancy n) ≤ 1 then (1 : ℝ) else 0) := by
    intro X
    rw [Finset.natCast_card_filter]
  -- pointwise sandwich
  have hup : ∀ δ : ℝ, 0 < δ → ∀ p : ℝ × ℝ,
      (if G p ≤ 1 then (1 : ℝ) else 0) ≤ clampBCF _ (hFp δ) p := by
    intro δ hδ p
    rw [clampBCF_apply]
    split_ifs with h
    · rw [clamp01_of_one_le]
      rw [le_div_iff₀ hδ]
      linarith
    · exact clamp01_nonneg _
  have hlo : ∀ δ : ℝ, 0 < δ → ∀ p : ℝ × ℝ,
      clampBCF _ (hFm δ) p ≤ (if G p ≤ 1 then (1 : ℝ) else 0) := by
    intro δ hδ p
    rw [clampBCF_apply]
    split_ifs with h
    · exact clamp01_le_one _
    · rw [clamp01_of_nonpos]
      exact div_nonpos_of_nonpos_of_nonneg (by linarith [not_le.1 h]) hδ.le
  -- the limits of the test functions
  have hprodfin : IsFiniteMeasure ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod μ) := inferInstance
  have hIup : ∀ δ : ℝ, 0 < δ →
      ∫ p, clampBCF _ (hFp δ) p ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod μ) ≤ (1 + δ) * W := by
    intro δ hδ
    have hi := (clampBCF _ (hFp δ)).integrable ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod μ)
    rw [integral_prod_symm _ hi, hW, ← integral_const_mul]
    refine integral_mono_ae hi.integral_prod_right (hWint.const_mul _) ?_
    filter_upwards [hae] with h hh
    simp only [clampBCF_apply, G]
    have := inner_upper hh hδ
    calc ∫ x in Set.Icc (0 : ℝ) 1, clamp01 ((1 + δ - x * (s + σ * (h - 1))) / δ)
        ≤ (1 + δ) / (s + σ * (h - 1)) := this
      _ = (1 + δ) * (1 / (s + σ * (h - 1))) := by ring
  have hIlo : ∀ δ : ℝ, 0 < δ → δ < 1 →
      (1 - δ) * W ≤ ∫ p, clampBCF _ (hFm δ) p ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod μ) := by
    intro δ hδ hδ1
    have hi := (clampBCF _ (hFm δ)).integrable ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod μ)
    rw [integral_prod_symm _ hi, hW, ← integral_const_mul]
    refine integral_mono_ae (hWint.const_mul _) hi.integral_prod_right ?_
    filter_upwards [hae] with h hh
    simp only [clampBCF_apply, G]
    have := inner_lower hh hδ hδ1
    calc (1 - δ) * (1 / (s + σ * (h - 1))) = (1 - δ) / (s + σ * (h - 1)) := by ring
      _ ≤ ∫ x in Set.Icc (0 : ℝ) 1, clamp01 ((1 - x * (s + σ * (h - 1))) / δ) := this
  rw [tendsto_order]
  constructor
  · intro a' ha'
    set δ : ℝ := min (1 / 2) ((W - a') / (2 * (W + 1))) with hδdef
    have hδ : 0 < δ := lt_min (by norm_num) (div_pos (by linarith) (by linarith))
    have hδ1 : δ < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
    have hδW : δ * (W + 1) ≤ (W - a') / 2 := by
      have := min_le_right (1 / 2 : ℝ) ((W - a') / (2 * (W + 1)))
      rw [← hδdef] at this
      calc δ * (W + 1) ≤ (W - a') / (2 * (W + 1)) * (W + 1) :=
            mul_le_mul_of_nonneg_right this (by linarith)
        _ = (W - a') / 2 := by field_simp
    have hlt : a' < ∫ p, clampBCF _ (hFm δ) p ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod μ) := by
      have := hIlo δ hδ hδ1
      nlinarith
    filter_upwards [(tendsto_order.1 (hJ (clampBCF _ (hFm δ)))).1 a' hlt,
      eventually_gt_atTop (0 : ℝ)] with X hX hXpos
    refine lt_of_lt_of_le hX ?_
    rw [hcount]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun n _ => hlo δ hδ _) (by positivity)
  · intro a' ha'
    set δ : ℝ := min (1 / 2) ((a' - W) / (2 * (W + 1))) with hδdef
    have hδ : 0 < δ := lt_min (by norm_num) (div_pos (by linarith) (by linarith))
    have hδW : δ * (W + 1) ≤ (a' - W) / 2 := by
      have := min_le_right (1 / 2 : ℝ) ((a' - W) / (2 * (W + 1)))
      rw [← hδdef] at this
      calc δ * (W + 1) ≤ (a' - W) / (2 * (W + 1)) * (W + 1) :=
            mul_le_mul_of_nonneg_right this (by linarith)
        _ = (a' - W) / 2 := by field_simp
    have hlt : ∫ p, clampBCF _ (hFp δ) p ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod μ) < a' := by
      have := hIup δ hδ
      nlinarith
    filter_upwards [(tendsto_order.1 (hJ (clampBCF _ (hFp δ)))).2 a' hlt,
      eventually_gt_atTop (0 : ℝ)] with X hX hXpos
    refine lt_of_le_of_lt ?_ hX
    rw [hcount]
    exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun n _ => hup δ hδ _) (by positivity)

/-- The tangent-line (Jensen) inequality `1/(s + σx) ≥ 1/c − σ(x − m)/c²`, `c = s + σm`. -/
theorem tangent_le {s σ x m : ℝ} (hc : 0 < s + σ * m) (hx : 0 < s + σ * x) :
    1 / (s + σ * m) - σ * (x - m) / (s + σ * m) ^ 2 ≤ 1 / (s + σ * x) := by
  have key : 1 / (s + σ * x) - (1 / (s + σ * m) - σ * (x - m) / (s + σ * m) ^ 2) =
      (σ * (x - m)) ^ 2 / ((s + σ * m) ^ 2 * (s + σ * x)) := by
    field_simp
    ring
  have : 0 ≤ (σ * (x - m)) ^ 2 / ((s + σ * m) ^ 2 * (s + σ * x)) := by positivity
  linarith

theorem ae_one_le_of_Iio {μ : Measure ℝ} (hsupp : μ (Set.Iio 1) = 0) : ∀ᵐ h ∂μ, (1 : ℝ) ≤ h := by
  rw [ae_iff]
  have : {a : ℝ | ¬ 1 ≤ a} = Set.Iio 1 := by
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_Iio, not_le]
  rw [this]
  exact hsupp

theorem integrable_inv_affine {μ : Measure ℝ} [IsFiniteMeasure μ] (hsupp : μ (Set.Iio 1) = 0)
    {s σ : ℝ} (hs : 1 ≤ s) (hσ : 0 ≤ σ) : Integrable (fun h : ℝ => 1 / (s + σ * (h - 1))) μ := by
  have hmeas : Measurable (fun h : ℝ => 1 / (s + σ * (h - 1))) := by fun_prop
  refine Integrable.mono' (integrable_const (1 : ℝ)) hmeas.aestronglyMeasurable ?_
  filter_upwards [ae_one_le_of_Iio hsupp] with h hh
  have hg : 1 ≤ s + σ * (h - 1) := by nlinarith
  rw [Real.norm_eq_abs, abs_of_pos (by positivity), div_le_one (by linarith)]
  exact hg

theorem progLaw_Iio_one (hPL : Fact_DaddProgressionLaws) {a : ℕ} (ha : a ∈ classesQ) :
    progLaw 5 a (Set.Iio 1) = 0 := by
  have hle : progLaw 5 a (Set.Iio 1) ≤ nuQ (Set.Iio 1) := by
    rw [nuQ_eq, Measure.finsetSum_apply]
    exact Finset.single_le_sum (f := fun b => progLaw 5 b (Set.Iio 1)) (fun _ _ => zero_le) ha
  rw [nuQ_Iio_one hPL] at hle
  exact le_antisymm hle zero_le

theorem sourceIntensity_link :
    Principia.Erdos1054.Spine.Link_Step_DaddCollisionSourceIntensity := by
  intro hAff hJL hPL hFML D hD
  haveI := nuQ_finite hPL
  have hal : 1 ≤ aliquot D := by
    rcases mem_cores hD with rfl | rfl | rfl | rfl <;> decide
  have hs1 : (1 : ℝ) ≤ (aliquot D : ℝ) := by exact_mod_cast hal
  have hσ0 : (0 : ℝ) ≤ (sig D : ℝ) := Nat.cast_nonneg _
  -- per-class radial limits
  have hclass : ∀ a ∈ classesQ, Tendsto (fun X : ℝ => (1 / X) *
      (((((Finset.Icc 1 ⌊X⌋₊).filter (fun n : ℕ => n % 60 = a)).filter
        (fun n : ℕ => (n : ℝ) / X * ((aliquot D : ℝ) + (sig D : ℝ) * (abundancy n - 1)) ≤ 1)).card :
          ℕ) : ℝ)) atTop
      (𝓝 (∫ h, 1 / ((aliquot D : ℝ) + (sig D : ℝ) * (h - 1)) ∂(progLaw 5 a))) := by
    intro a ha
    haveI := progLaw_finite hPL a
    have ha60 : a < 60 := by
      unfold classesQ at ha
      rw [Finset.mem_filter, Finset.mem_range] at ha
      exact ha.1
    refine radial_limit (progLaw_Iio_one hPL ha) hs1 hσ0
      (P := fun X => (Finset.Icc 1 ⌊X⌋₊).filter (fun n : ℕ => n % 60 = a)) (fun φ => ?_)
    have h := hJL 5 a (by norm_num) 1 one_pos φ
    rw [lcmUpTo_five', Nat.mod_eq_of_lt ha60] at h
    simp only [one_mul] at h
    exact h
  have hsum := tendsto_finsetSum classesQ hclass
  have hW : ∑ a ∈ classesQ, ∫ h, 1 / ((aliquot D : ℝ) + (sig D : ℝ) * (h - 1)) ∂(progLaw 5 a) =
      ∫ h, 1 / ((aliquot D : ℝ) + (sig D : ℝ) * (h - 1)) ∂nuQ := by
    rw [nuQ_eq, integral_finsetSum_measure]
    intro a ha
    haveI := progLaw_finite hPL a
    exact integrable_inv_affine (progLaw_Iio_one hPL ha) hs1 hσ0
  refine ⟨∫ h, 1 / ((aliquot D : ℝ) + (sig D : ℝ) * (h - 1)) ∂nuQ, ?_, rfl, ?_⟩
  · rw [← hW]
    refine hsum.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
    -- the class decomposition of the count
    have hA : ∀ u : ℕ, 1 ≤ u → Nat.Coprime u 30 →
        ((aliquot (D * u) : ℝ) ≤ X ↔
          (u : ℝ) / X * ((aliquot D : ℝ) + (sig D : ℝ) * (abundancy u - 1)) ≤ 1) := by
      intro u hu1 hu
      rw [(hAff D hD u hu1 hu).2, div_mul_eq_mul_div, div_le_one hX]
    have hcard : ((Finset.Icc 1 ⌊X⌋₊).filter (fun u : ℕ =>
        Nat.Coprime u 30 ∧ (aliquot (D * u) : ℝ) ≤ X)).card =
        cnt {n : ℕ | Nat.Coprime n 30 ∧
          (n : ℝ) / X * ((aliquot D : ℝ) + (sig D : ℝ) * (abundancy n - 1)) ≤ 1} X := by
      unfold cnt
      congr 1
      ext u
      simp only [Finset.mem_filter, Finset.mem_Icc, Set.mem_setOf_eq]
      constructor
      · rintro ⟨hu, hc, hle⟩
        exact ⟨hu, hc, (hA u hu.1 hc).1 hle⟩
      · rintro ⟨hu, hc, hle⟩
        exact ⟨hu, hc, (hA u hu.1 hc).2 hle⟩
    have hcls : ∀ a : ℕ, (((Finset.Icc 1 ⌊X⌋₊).filter (fun n : ℕ => n % 60 = a)).filter
        (fun n : ℕ => (n : ℝ) / X * ((aliquot D : ℝ) + (sig D : ℝ) * (abundancy n - 1)) ≤ 1)).card =
        cnt {n : ℕ | n % 60 = a ∧
          (n : ℝ) / X * ((aliquot D : ℝ) + (sig D : ℝ) * (abundancy n - 1)) ≤ 1} X := by
      intro a
      unfold cnt
      rw [Finset.filter_filter]
      congr 1
      ext u
      simp only [Finset.mem_filter, Set.mem_setOf_eq]
    rw [hcard, cnt_split_mod (A := classesQ) (Q := 60) (fun n => mem_classesQ_mod), Nat.cast_sum,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hcls a]
  · -- Jensen's inequality, in tangent-line form
    obtain ⟨hmass, hint, hmom⟩ := hFML
    have hD5 : Delta 5 = 4 / 15 := delta_five
    have hD5pos : (0 : ℝ) < Delta 5 := by rw [hD5]; norm_num
    have hreal : nuQ.real Set.univ = Delta 5 := by
      rw [measureReal_def, hmass, ENNReal.toReal_ofReal hD5pos.le]
    have hI : ∫ h, (h - 1) ∂nuQ = Delta 5 * collisionH := by
      have := hmom
      field_simp at this
      linarith
    have hm := collisionH_pos
    set s : ℝ := (aliquot D : ℝ) with hs
    set σ : ℝ := (sig D : ℝ) with hσ
    set m : ℝ := collisionH with hmdef
    have hc : 0 < s + σ * m := by positivity
    have hpt : ∀ᵐ h ∂nuQ, (1 / (s + σ * m) + σ * m / (s + σ * m) ^ 2) -
        σ / (s + σ * m) ^ 2 * (h - 1) ≤ 1 / (s + σ * (h - 1)) := by
      filter_upwards [ae_one_le_nuQ hPL] with h hh
      have hx : 0 < s + σ * (h - 1) := by nlinarith
      have := tangent_le (x := h - 1) hc hx
      calc (1 / (s + σ * m) + σ * m / (s + σ * m) ^ 2) - σ / (s + σ * m) ^ 2 * (h - 1)
          = 1 / (s + σ * m) - σ * ((h - 1) - m) / (s + σ * m) ^ 2 := by ring
        _ ≤ 1 / (s + σ * (h - 1)) := this
    have hlinint : Integrable (fun h : ℝ => (1 / (s + σ * m) + σ * m / (s + σ * m) ^ 2) -
        σ / (s + σ * m) ^ 2 * (h - 1)) nuQ :=
      (integrable_const _).sub (hint.const_mul _)
    have hlin : ∫ h, ((1 / (s + σ * m) + σ * m / (s + σ * m) ^ 2) -
        σ / (s + σ * m) ^ 2 * (h - 1)) ∂nuQ = Delta 5 / (s + σ * m) := by
      rw [integral_sub (integrable_const _) (hint.const_mul _), integral_const, smul_eq_mul,
        integral_const_mul, hreal, hI]
      field_simp
      ring
    rw [← hlin]
    exact integral_mono_ae hlinint (integrable_inv_affine (nuQ_Iio_one hPL) hs1 hσ0) hpt

end Principia.Erdos1054.Proofs.Collision7

namespace Principia.Erdos1054.Proofs

/-- `Step_DaddCollisionArithmetic` (leaf). Paper lines 3161–3170. -/
theorem leaf_Step_DaddCollisionArithmetic : Principia.Erdos1054.Step_DaddCollisionArithmetic :=
  Collision7.arith

/-- `Step_DaddCollisionCores` (leaf). Paper lines 3084, 3157–3160. -/
theorem leaf_Step_DaddCollisionCores : Principia.Erdos1054.Step_DaddCollisionCores :=
  Collision7.cores

/-- `Step_DaddCollisionH` (leaf). Paper lines 3102–3105, 3156. -/
theorem leaf_Step_DaddCollisionH : Principia.Erdos1054.Step_DaddCollisionH :=
  Collision7.stepH

/-- `Eq_DaddCollisionAffine` (leaf). Paper lines 3087–3094. -/
theorem leaf_Eq_DaddCollisionAffine : Principia.Erdos1054.Eq_DaddCollisionAffine :=
  Collision7.affine

/-- `Link_Step_DaddCollisionWitness`. Paper lines 3095–3096. -/
theorem link_Step_DaddCollisionWitness :
    Principia.Erdos1054.Spine.Link_Step_DaddCollisionWitness :=
  Collision7.witness_link

/-- `Link_Step_DaddCollisionCombine`. Paper lines 3146–3154. -/
theorem link_Step_DaddCollisionCombine :
    Principia.Erdos1054.Spine.Link_Step_DaddCollisionCombine :=
  Collision7.combine_link

/-- `Link_Step_DaddCollisionExplicit`. Paper lines 3161–3170. -/
theorem link_Step_DaddCollisionExplicit :
    Principia.Erdos1054.Spine.Link_Step_DaddCollisionExplicit :=
  Collision7.explicit_link

/-- `Link_Prop_DaddCollisionLowerBound`. Paper lines 3076–3174. -/
theorem link_Prop_DaddCollisionLowerBound :
    Principia.Erdos1054.Spine.Link_Prop_DaddCollisionLowerBound :=
  Collision7.lowerBound_link

/-- `Link_Step_DaddCollisionSupport`. Paper lines 3050–3057. -/
theorem link_Step_DaddCollisionSupport :
    Principia.Erdos1054.Spine.Link_Step_DaddCollisionSupport :=
  Collision7.support_link

/-- `Link_Eq_DaddCollisionCriterion`. Paper lines 3038–3042, 3058–3061. -/
theorem link_Eq_DaddCollisionCriterion :
    Principia.Erdos1054.Spine.Link_Eq_DaddCollisionCriterion :=
  Collision7.eqCriterion_link

/-- `Link_Step_DaddCollisionCylinder`. Paper lines 3120–3136. -/
theorem link_Step_DaddCollisionCylinder :
    Principia.Erdos1054.Spine.Link_Step_DaddCollisionCylinder :=
  Collision7.cylinder_link

/-- `Link_Step_DaddCollisionPerCore`. Paper lines 3137–3145. -/
theorem link_Step_DaddCollisionPerCore :
    Principia.Erdos1054.Spine.Link_Step_DaddCollisionPerCore :=
  Collision7.perCore_link

/-- `Link_Step_DaddCollisionFirstMoment`. Paper lines 3099–3105. -/
theorem link_Step_DaddCollisionFirstMoment :
    Principia.Erdos1054.Spine.Link_Step_DaddCollisionFirstMoment :=
  Collision7.firstMoment_link

/-- `Link_Step_DaddCollisionFirstMomentLaw`. Paper lines 3098–3108. -/
theorem link_Step_DaddCollisionFirstMomentLaw :
    Principia.Erdos1054.Spine.Link_Step_DaddCollisionFirstMomentLaw :=
  Collision7.firstMomentLaw_link

/-- `Link_Step_DaddCollisionSourceIntensity`. Paper lines 3109–3118. -/
theorem link_Step_DaddCollisionSourceIntensity :
    Principia.Erdos1054.Spine.Link_Step_DaddCollisionSourceIntensity :=
  Collision7.sourceIntensity_link

/-- `Link_Prop_DaddCollisionCriterion`. Paper lines 3032–3072. -/
theorem link_Prop_DaddCollisionCriterion :
    Principia.Erdos1054.Spine.Link_Prop_DaddCollisionCriterion :=
  Collision7.propCriterion_link

end Principia.Erdos1054.Proofs
