/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Erdos1054.Spine
import Principia.Erdos1054.Basic
import Principia.Erdos1054.Density
import Mathlib.NumberTheory.PrimesCongruentOne
import Mathlib.Data.ZMod.Units
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Squarefree
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Normed.Group.Tannery

set_option autoImplicit false

/-!
# Erdős 1054 (EP1054.tex) — `prop:class-first-moment` (lines 2283–2435)

Every obligation of the proof of `prop:class-first-moment`, as the spine states it:

* leaves: `Eq_HGcd`, `Eq_UClass`, `Coverage.Step_SeDensity`, `Coverage.Step_HeRatio`,
  `Coverage.Step_SeMultiplesDens`, `Coverage.Step_DistinctPairs`;
* links: `Eq_He`, `Coverage.Step_ClassResidue`, `Eq_RepresentingRatio`, `Coverage.Disp_HeMean`,
  `Coverage.Step_GeLowerDens`, `Eq_ClassLower`, `Coverage.Disp_MertensCoprimeQ` (from
  `Std_Mertens3`), `Coverage.Disp_ClassPrimeSum` (from `Std_PNT_AP`),
  `Prop_ClassFirstMoment_bound`, `Prop_ClassFirstMoment_tendsto`.

`Prop_ClassFirstMoment` itself is `And.intro` of the last two and is assembled by the spine.

## Proof notes (where the Lean argument differs in detail from the paper's prose)

* `Eq_HGcd`: instead of the paper's per-prime-power construction with lifting the exponent, one
  prime `q ≡ 1 (mod Q)` (Mathlib's elementary `Nat.exists_prime_gt_modEq_one`) and `h = q^{d₀−1}`
  suffice: `σ(h) = 1 + q + ⋯ + q^{d₀−1} ≡ d₀ (mod Q)`, so `gcd(σ(h), Q) = gcd(d₀, Q) = d₀`.
* `Coverage.Step_SeDensity` / `Step_SeMultiplesDens`: the period is `Q · P₀` (resp. `a Q P₀`) with
  `P₀ = ∏_{p ≤ e, p ∤ Q} p`; one period contains exactly `φ(P₀)` members (`card_ap_coprime`, an
  affine bijection mod `P₀`), and `φ(P₀)/P₀ = ∏_{p ≤ e, p ∤ Q}(1 − 1/p)`.
* `Coverage.Disp_ClassPrimeSum` needs no partial summation: `π(Z)/log Z ≤ S(Z)` termwise, and
  `S(Z) ≤ 2(Y+1) + π(Z)/log Y` with `Y = Z/(log Z)³`, both sides `∼ Z/(φ(Q) log² Z)` by `Std_PNT_AP`.
* `Coverage.Disp_HeMean`: the divisor sum is swapped into `∑_a fT T a` with `fT T a ≤ a^{-2}` and
  Mathlib's `tendsto_tsum_of_dominated_convergence` (Tannery) does the interchange.
* `Eq_ClassLower`: the sequence in `lamLower` is bounded (`sum_rt_le`, from `eq:moment` at `k = 2`,
  `E = 1` and `eq:reflection`), so Mathlib's `liminf` is the genuine one; the lower bound is the
  injection `(e, t) ↦ (e, h t)` into the pairs counted by `r_A` (`lower_count`).
-/

namespace Principia.Erdos1054.Proofs.ClassMoment

open Finset Filter
open scoped Topology

/-- `⌊(e : ℝ)⌋₊ = e`, so `primorialR e = primorial e`. -/
theorem primorialR_natCast (e : ℕ) : primorialR (e : ℝ) = primorial e := by
  unfold primorialR
  rw [Nat.floor_natCast]

/-- The context's arithmetic facts, unpacked. -/
theorem ctx_e_gt_h {Q ρ h u e : ℕ} (hc : Coverage.ClassCtx Q ρ h u e) : h < e := by
  obtain ⟨-, -, -, -, -, -, hlt, -⟩ := hc
  have := le_max_right 2 h
  have := le_max_left (max 2 h) Q
  omega

theorem ctx_e_gt_Q {Q ρ h u e : ℕ} (hc : Coverage.ClassCtx Q ρ h u e) : Q < e := by
  obtain ⟨-, -, -, -, -, -, hlt, -⟩ := hc
  have := le_max_right (max 2 h) Q
  omega

theorem ctx_e_gt_two {Q ρ h u e : ℕ} (hc : Coverage.ClassCtx Q ρ h u e) : 2 < e := by
  obtain ⟨-, -, -, -, -, -, hlt, -⟩ := hc
  have := le_max_left 2 h
  have := le_max_left (max 2 h) Q
  omega

/-- `Q ∣ e + 1` from `e ≡ −1 (mod Q)`. -/
theorem ctx_Q_dvd {Q ρ h u e : ℕ} (hc : Coverage.ClassCtx Q ρ h u e) : Q ∣ e + 1 := by
  obtain ⟨hQ, -, -, -, -, -, -, hmod⟩ := hc
  apply Nat.dvd_of_mod_eq_zero
  rw [Nat.add_mod, hmod, ← Nat.add_mod, Nat.sub_add_cancel hQ, Nat.mod_self]

/-- Every element of `𝒮_e` is coprime to every `1 ≤ m ≤ e`. -/
theorem Se_coprime_of_le {Q u e t : ℕ} (ht : t ∈ Coverage.Se Q u e) {m : ℕ} (hm : 1 ≤ m)
    (hme : m ≤ e) : Nat.Coprime t m := by
  obtain ⟨-, -, hcop⟩ := ht
  rw [primorialR_natCast] at hcop
  apply Nat.coprime_of_dvd
  intro p hp hpt hpm
  have hple : p ≤ e := (Nat.le_of_dvd (by omega) hpm).trans hme
  have hpd : p ∣ primorial e := (Nat.Prime.dvd_primorial_iff hp).2 hple
  have : p ∣ Nat.gcd t (primorial e) := Nat.dvd_gcd hpt hpd
  rw [hcop] at this
  exact hp.one_lt.ne' (Nat.dvd_one.1 this)

/-- `σ(n) ≥ n` for `n ≥ 1`. -/
theorem le_sig {n : ℕ} (hn : 1 ≤ n) : n ≤ sig n := by
  unfold sig
  rw [ArithmeticFunction.sigma_one_apply]
  exact Finset.single_le_sum (fun i _ => Nat.zero_le i) (Nat.mem_divisors_self n (by omega))

/-- `n ∑_{r ∣ n} 1/r = σ(n)`. -/
theorem mul_sum_inv_divisors (n : ℕ) :
    (n : ℝ) * ∑ r ∈ n.divisors, (1 : ℝ) / r = (sig n : ℝ) := by
  have h1 : sig n = ∑ d ∈ n.divisors, n / d := by
    unfold sig
    rw [ArithmeticFunction.sigma_one_apply]
    exact (Nat.sum_div_divisors n (fun d => d)).symm
  rw [h1, Nat.cast_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  have hrd : r ∣ n := Nat.dvd_of_mem_divisors hr
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hr).ne'
  rw [Nat.cast_div hrd hr0]
  ring

/-- `σ(e) = e + 1` for prime `e`. -/
theorem sig_prime {e : ℕ} (he : e.Prime) : sig e = e + 1 := by
  unfold sig
  have := ArithmeticFunction.sigma_one_apply_prime_pow (i := 1) he
  rw [pow_one] at this
  rw [this]
  simp [Finset.sum_range_succ]
  ring

/-! ## Leaves -/

theorem distinct_aux {Q ρ h u e e' t t' : ℕ} (hc : Coverage.ClassCtx Q ρ h u e)
    (hc' : Coverage.ClassCtx Q ρ h u e') (ht' : t' ∈ Coverage.Se Q u e') (hlt : e < e')
    (heq : e * h * t = e' * h * t') : False := by
  have hep : e.Prime := hc.2.2.2.2.2.1
  have hep' : e'.Prime := hc'.2.2.2.2.2.1
  have hhe : h < e := ctx_e_gt_h hc
  have hh1 : 1 ≤ h := hc.2.1
  have hdvd : e ∣ e' * h * t' := by rw [← heq, mul_assoc]; exact dvd_mul_right e _
  rcases (Nat.Prime.dvd_mul hep).1 hdvd with h1 | h1
  · rcases (Nat.Prime.dvd_mul hep).1 h1 with h2 | h2
    · rcases (Nat.dvd_prime hep').1 h2 with h3 | h3
      · exact hep.one_lt.ne' h3
      · omega
    · have := Nat.le_of_dvd (by omega) h2
      omega
  · have hcop : Nat.Coprime t' e := Se_coprime_of_le ht' hep.one_lt.le hlt.le
    have : e ∣ Nat.gcd t' e := Nat.dvd_gcd h1 dvd_rfl
    rw [hcop] at this
    exact hep.one_lt.ne' (Nat.dvd_one.1 this)

theorem sum_filter_one_lt_divisors {t : ℕ} (ht : 1 ≤ t) :
    ∑ a ∈ t.divisors.filter (1 < ·), (1 : ℝ) / a = ∑ a ∈ t.divisors, (1 : ℝ) / a - 1 := by
  rw [← Finset.sum_filter_add_sum_filter_not t.divisors (1 < ·)]
  have hset : t.divisors.filter (fun a => ¬ 1 < a) = {1} := by
    ext a
    simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_singleton, not_lt]
    constructor
    · rintro ⟨⟨hat, ht0⟩, ha1⟩
      have : 0 < a := Nat.pos_of_dvd_of_pos hat (by omega)
      omega
    · rintro rfl
      exact ⟨⟨one_dvd t, by omega⟩, le_rfl⟩
  rw [hset, Finset.sum_singleton]
  simp

/-- Casting `s(t) = σ(t) − t`. -/
theorem aliquot_cast {t : ℕ} (ht : 1 ≤ t) : (aliquot t : ℝ) = (sig t : ℝ) - t := by
  unfold aliquot
  rw [Nat.cast_sub (le_sig ht)]

theorem He_cast (e t : ℕ) (ht : 1 ≤ t) :
    (Coverage.He e t : ℝ) = t + ((e : ℝ) + 1) * ((sig t : ℝ) - t) := by
  unfold Coverage.He
  rw [Nat.cast_add, Nat.cast_mul, aliquot_cast ht]
  push_cast
  ring

theorem le_He (e t : ℕ) : t ≤ Coverage.He e t := by
  unfold Coverage.He
  omega

/-- For `t ∈ 𝒮_e`, the divisors of `e h t` below `e` are exactly the divisors of `h`. -/
theorem divisors_lt_e_eq {Q ρ h u e t : ℕ} (hc : Coverage.ClassCtx Q ρ h u e)
    (ht : t ∈ Coverage.Se Q u e) :
    (e * (h * t)).divisors.filter (fun r => ¬ e ≤ r) = h.divisors := by
  have hep : e.Prime := hc.2.2.2.2.2.1
  have hhe : h < e := ctx_e_gt_h hc
  have hh1 : 1 ≤ h := hc.2.1
  have ht1 : 1 ≤ t := ht.1
  have hn0 : e * (h * t) ≠ 0 := (Nat.mul_pos hep.pos (Nat.mul_pos hh1 ht1)).ne'
  ext r
  simp only [Finset.mem_filter, Nat.mem_divisors, not_le]
  constructor
  · rintro ⟨⟨hr, -⟩, hre⟩
    refine ⟨?_, by omega⟩
    have hr0 : 0 < r := Nat.pos_of_dvd_of_pos hr (Nat.pos_of_ne_zero hn0)
    have hcre : Nat.Coprime r e := Nat.Coprime.symm
      ((Nat.Prime.coprime_iff_not_dvd hep).2 (fun hd => by
        have := Nat.le_of_dvd hr0 hd
        omega))
    have hcrt : Nat.Coprime r t := (Se_coprime_of_le ht hr0 hre.le).symm
    have h1 : r ∣ h * t := hcre.dvd_of_dvd_mul_left hr
    exact hcrt.dvd_of_dvd_mul_right h1
  · rintro ⟨hr, -⟩
    refine ⟨⟨Dvd.dvd.mul_left (Dvd.dvd.mul_right hr t) e, hn0⟩, ?_⟩
    have := Nat.le_of_dvd (by omega) hr
    omega

end Principia.Erdos1054.Proofs.ClassMoment

namespace Principia.Erdos1054.Proofs

open Principia.Erdos1054.Proofs.ClassMoment

theorem leaf_Coverage_Step_DistinctPairs : Coverage.Step_DistinctPairs := by
  intro Q ρ h u e e' t t' hc hc' ht ht' heq
  rcases lt_trichotomy e e' with hlt | hEq | hgt
  · exact (distinct_aux hc hc' ht' hlt heq).elim
  · subst hEq
    refine ⟨rfl, ?_⟩
    have hpos : 0 < e * h := Nat.mul_pos (hc.2.2.2.2.2.1.pos) hc.2.1
    exact Nat.eq_of_mul_eq_mul_left hpos heq
  · exact (distinct_aux hc' hc ht hgt heq.symm).elim

theorem leaf_Eq_HGcd : Eq_HGcd := by
  intro Q hQ ρ
  obtain ⟨q, hq, -, hq1⟩ := Nat.exists_prime_gt_modEq_one 0 (show Q ≠ 0 by omega)
  set d0 := Nat.gcd ρ Q with hd0
  have hd0pos : 0 < d0 := Nat.gcd_pos_of_pos_right _ hQ
  refine ⟨q ^ (d0 - 1), Nat.one_le_iff_ne_zero.2 (pow_ne_zero _ hq.ne_zero), ?_⟩
  have hsig : sig (q ^ (d0 - 1)) = ∑ k ∈ Finset.range d0, q ^ k := by
    unfold sig
    rw [ArithmeticFunction.sigma_one_apply_prime_pow hq, Nat.sub_add_cancel hd0pos]
  have hmod : sig (q ^ (d0 - 1)) ≡ d0 [MOD Q] := by
    rw [hsig, ← ZMod.natCast_eq_natCast_iff]
    have hq' : (q : ZMod Q) = 1 := by
      rw [← Nat.cast_one, ZMod.natCast_eq_natCast_iff]
      exact hq1
    push_cast
    rw [hq']
    simp
  rw [hmod.gcd_eq, hd0]
  exact Nat.gcd_eq_left (Nat.gcd_dvd_right ρ Q)

theorem leaf_Eq_UClass : Eq_UClass := by
  intro Q hQ ρ h hg
  set s := sig h with hs
  set d := Nat.gcd s Q with hd
  have hdpos : 0 < d := Nat.gcd_pos_of_pos_right _ hQ
  have hdQ : d ∣ Q := Nat.gcd_dvd_right _ _
  have hds : d ∣ s := Nat.gcd_dvd_left _ _
  have hdρ : d ∣ ρ := by rw [hg]; exact Nat.gcd_dvd_left ρ Q
  set Q' := Q / d with hQ'
  have hQ'pos : 0 < Q' := Nat.div_pos (Nat.le_of_dvd hQ hdQ) hdpos
  have hcs : Nat.Coprime (s / d) Q' := Nat.coprime_div_gcd_div_gcd hdpos
  have hcρ : Nat.Coprime (ρ / d) Q' := by
    have hρpos : 0 < Nat.gcd ρ Q := Nat.gcd_pos_of_pos_right _ hQ
    have := Nat.coprime_div_gcd_div_gcd hρpos
    rwa [← hg] at this
  haveI : NeZero Q' := ⟨hQ'pos.ne'⟩
  haveI : NeZero Q := ⟨by omega⟩
  obtain ⟨w, hw⟩ := ZMod.unitsMap_surjective (m := Q) (n := Q') (Nat.div_dvd_of_dvd hdQ)
    ((ZMod.unitOfCoprime (s / d) hcs)⁻¹ * ZMod.unitOfCoprime (ρ / d) hcρ)
  refine ⟨(w : ZMod Q).val, ZMod.val_coe_unit_coprime w, ?_⟩
  have key : (s / d) * (w : ZMod Q).val ≡ ρ / d [MOD Q'] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    have hv : (((w : ZMod Q).val : ℕ) : ZMod Q') =
        (((ZMod.unitOfCoprime (s / d) hcs)⁻¹ * ZMod.unitOfCoprime (ρ / d) hcρ :
          (ZMod Q')ˣ) : ZMod Q') := by
      rw [← hw, ZMod.unitsMap_val, ZMod.cast_eq_val]
    push_cast
    rw [hv, Units.val_mul, ← mul_assoc]
    have h1 : ((s / d : ℕ) : ZMod Q') = ((ZMod.unitOfCoprime (s / d) hcs : (ZMod Q')ˣ) : ZMod Q') :=
      (ZMod.coe_unitOfCoprime _ _).symm
    have h2 : ((ρ / d : ℕ) : ZMod Q') = ((ZMod.unitOfCoprime (ρ / d) hcρ : (ZMod Q')ˣ) : ZMod Q') :=
      (ZMod.coe_unitOfCoprime _ _).symm
    rw [h1, h2, Units.mul_inv, one_mul]
  have := key.mul_left' d
  rwa [← mul_assoc, Nat.mul_div_cancel' hds, Nat.mul_div_cancel' hdρ,
    Nat.mul_div_cancel' hdQ] at this

theorem leaf_Coverage_Step_HeRatio : Coverage.Step_HeRatio := by
  intro Q ρ h u e hc t ht
  have ht1 : 1 ≤ t := ht.1
  have htR : (t : ℝ) ≠ 0 := by exact_mod_cast (show t ≠ 0 by omega)
  rw [sum_filter_one_lt_divisors ht1, He_cast e t ht1, div_eq_iff htR, ← mul_sum_inv_divisors t]
  ring

theorem link_Eq_He : Spine.Link_Eq_He := by
  intro _hSe Q ρ h u e hc t ht
  have hep : e.Prime := hc.2.2.2.2.2.1
  have hhe : h < e := ctx_e_gt_h hc
  have hh1 : 1 ≤ h := hc.2.1
  have ht1 : 1 ≤ t := ht.1
  have h2 : Coverage.He e t + e * t = (e + 1) * sig t := by
    obtain ⟨a, ha⟩ := Nat.exists_eq_add_of_le (le_sig ht1)
    unfold Coverage.He aliquot
    rw [ha, Nat.add_sub_cancel_left]
    ring
  refine ⟨?_, h2⟩
  have hceh : Nat.Coprime e h := (Nat.Prime.coprime_iff_not_dvd hep).2 (fun hd => by
    have := Nat.le_of_dvd hh1 hd
    omega)
  have hcet : Nat.Coprime e t := (Se_coprime_of_le ht hep.one_lt.le le_rfl).symm
  have hcht : Nat.Coprime h t := (Se_coprime_of_le ht hh1 hhe.le).symm
  have hsign : sig (e * (h * t)) = (e + 1) * (sig h * sig t) := by
    unfold sig
    rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (hceh.mul_right hcet),
      ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcht]
    rw [show ArithmeticFunction.sigma 1 e = e + 1 from sig_prime hep]
  have hF := reflection e (h * t) hep.one_lt.le (Nat.mul_pos hh1 ht1)
  have hsplit := Finset.sum_filter_add_sum_filter_not (e * (h * t)).divisors (fun r => e ≤ r)
    (fun r => (1 : ℝ) / r)
  rw [divisors_lt_e_eq hc ht] at hsplit
  have hg : g e (e * (h * t)) =
      ∑ r ∈ (e * (h * t)).divisors.filter (fun r => e ≤ r), (1 : ℝ) / r := rfl
  rw [← hg] at hsplit
  have hn := mul_sum_inv_divisors (e * (h * t))
  have hhs := mul_sum_inv_divisors h
  have h2R : (Coverage.He e t : ℝ) + e * t = (e + 1) * (sig t : ℝ) := by exact_mod_cast h2
  have hsignR : (sig (e * (h * t)) : ℝ) = (e + 1) * ((sig h : ℝ) * sig t) := by
    exact_mod_cast hsign
  have goalR : (F e (h * t) : ℝ) = (sig h : ℝ) * Coverage.He e t := by
    push_cast at hF hn
    rw [hF]
    linear_combination (↑e * (↑h * ↑t)) * hsplit + hn - (↑e * ↑t) * hhs + hsignR -
      (sig h : ℝ) * h2R
  exact_mod_cast goalR

theorem link_Coverage_Step_ClassResidue : Spine.Link_Coverage_Step_ClassResidue := by
  intro hHe Q ρ h u e hc t ht
  obtain ⟨hF, -⟩ := hHe Q ρ h u e hc t ht
  have hQd := ctx_Q_dvd hc
  have h1 : Coverage.He e t ≡ t [MOD Q] := by
    unfold Coverage.He
    have h0 : (e + 1) * aliquot t ≡ 0 [MOD Q] :=
      Nat.modEq_zero_iff_dvd.2 (dvd_mul_of_dvd_left hQd _)
    have h3 := h0.add_left t
    rwa [add_zero] at h3
  have h2 : F e (h * t) ≡ sig h * t [MOD Q] := by
    rw [hF]
    exact h1.mul_left _
  refine ⟨h2, ?_⟩
  have htu : t ≡ u [MOD Q] := ht.2.1
  exact h2.trans ((htu.mul_left _).trans hc.2.2.2.2.1)

theorem link_Eq_RepresentingRatio : Spine.Link_Eq_RepresentingRatio := by
  intro hHe Q ρ h u e hc t ht
  obtain ⟨hF, -⟩ := hHe Q ρ h u e hc t ht
  have hh1 : 1 ≤ h := hc.2.1
  have ht1 : 1 ≤ t := ht.1
  have hs1 : 1 ≤ sig h := le_trans hh1 (le_sig hh1)
  have hsR : (1 : ℝ) ≤ sig h := by exact_mod_cast hs1
  have htR : (0 : ℝ) < t := by exact_mod_cast ht1
  have hHeR : (t : ℝ) ≤ Coverage.He e t := by exact_mod_cast le_He e t
  constructor
  · rw [hF]
    push_cast
    rw [div_le_div_iff₀ (mul_pos (by linarith) (by linarith)) (by linarith)]
    have hnn : (0 : ℝ) ≤ e * h * sig h := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hHeR hnn]
  · exact div_le_self (by positivity) hsR

end Principia.Erdos1054.Proofs

namespace Principia.Erdos1054.Proofs.ClassMoment

open Finset Filter
open scoped Topology

/-- `A / (log A)^n → ∞`. -/
theorem tendsto_div_log_pow_atTop (n : ℕ) :
    Tendsto (fun A : ℝ => A / Real.log A ^ n) atTop atTop := by
  have h0 : Tendsto (fun x : ℝ => Real.log x ^ n / x) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 n one_ne_zero
    · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
      exact Set.mem_Ioi.2 (div_pos (pow_pos (Real.log_pos hx) n) (by linarith))
  refine h0.inv_tendsto_nhdsGT_zero.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  rw [Pi.inv_apply, inv_div]

/-- `∏_{p ∣ Q} (1 − 1/p) = φ(Q)/Q`. -/
theorem prod_primeFactors_one_sub {Q : ℕ} (hQ : 1 ≤ Q) :
    ∏ p ∈ Q.primeFactors, (1 - 1 / (p : ℝ)) = (Q.totient : ℝ) / Q := by
  have h := Nat.totient_eq_mul_prod_factors Q
  have hR : ((Q.totient : ℚ) : ℝ) = ((Q * ∏ p ∈ Q.primeFactors, (1 - (p : ℚ)⁻¹) : ℚ) : ℝ) := by
    rw [h]
  push_cast at hR
  have hQR : (Q : ℝ) ≠ 0 := by exact_mod_cast (show Q ≠ 0 by omega)
  rw [eq_div_iff hQR, hR]
  simp_rw [one_div]
  ring

/-- For `n ≥ Q ≥ 1`: `∏_{p ≤ n} (1 − 1/p) = (φ(Q)/Q) ∏_{p ≤ n, p ∤ Q} (1 − 1/p)`. -/
theorem prod_primes_split {Q n : ℕ} (hQ : 1 ≤ Q) (hn : Q ≤ n) :
    ∏ p ∈ (Finset.range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ)) =
      (Q.totient : ℝ) / Q *
        ∏ p ∈ (Finset.Iic n).filter (fun p : ℕ => p.Prime ∧ ¬ p ∣ Q), (1 - 1 / (p : ℝ)) := by
  rw [← Finset.prod_filter_mul_prod_filter_not ((Finset.range (n + 1)).filter Nat.Prime)
    (fun p => p ∣ Q), ← prod_primeFactors_one_sub hQ]
  congr 1
  · congr 1
    ext p
    simp only [Finset.mem_filter, Finset.mem_range, Nat.mem_primeFactors]
    constructor
    · rintro ⟨⟨-, hp⟩, hpQ⟩
      exact ⟨hp, hpQ, by omega⟩
    · rintro ⟨hp, hpQ, -⟩
      exact ⟨⟨by have := Nat.le_of_dvd (by omega) hpQ; omega, hp⟩, hpQ⟩
  · congr 1
    ext p
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Iic]
    constructor
    · rintro ⟨⟨hp1, hp⟩, hpQ⟩
      exact ⟨by omega, hp, hpQ⟩
    · rintro ⟨hp1, hp, hpQ⟩
      exact ⟨⟨by omega, hp⟩, hpQ⟩

/-- Lower bound: `π(Z; Q, −1)/log Z ≤ ∑_{e ≤ Z, e ≡ −1} 1/log e` for `Z > 1`. -/
theorem primeSum_lower (Q : ℕ) {Z : ℝ} (hZ : 1 < Z) :
    (piAP Z Q (Q - 1) : ℝ) / Real.log Z ≤
      ∑ e ∈ (Finset.Iic ⌊Z⌋₊).filter (fun e : ℕ => e.Prime ∧ e % Q = (Q - 1) % Q),
        1 / Real.log e := by
  unfold piAP
  have h := Finset.card_nsmul_le_sum
    ((Finset.Iic ⌊Z⌋₊).filter (fun e : ℕ => e.Prime ∧ e % Q = (Q - 1) % Q))
    (fun e : ℕ => 1 / Real.log e) (1 / Real.log Z) (fun e he => by
      simp only [Finset.mem_filter, Finset.mem_Iic] at he
      have he2 : (2 : ℝ) ≤ e := by exact_mod_cast he.2.1.two_le
      have heZ : (e : ℝ) ≤ Z := (Nat.le_floor_iff (by linarith)).1 he.1
      have hle : 0 < Real.log e := Real.log_pos (by linarith)
      exact one_div_le_one_div_of_le hle (Real.log_le_log (by linarith) heZ))
  rw [nsmul_eq_mul, mul_one_div] at h
  exact h

/-- Upper bound: split at `Y > 1`. -/
theorem primeSum_upper (Q : ℕ) (Z : ℝ) {Y : ℝ} (hY : 1 < Y) :
    ∑ e ∈ (Finset.Iic ⌊Z⌋₊).filter (fun e : ℕ => e.Prime ∧ e % Q = (Q - 1) % Q),
        1 / Real.log e ≤ 2 * (Y + 1) + (piAP Z Q (Q - 1) : ℝ) / Real.log Y := by
  unfold piAP
  set A := (Finset.Iic ⌊Z⌋₊).filter (fun e : ℕ => e.Prime ∧ e % Q = (Q - 1) % Q) with hA
  rw [← Finset.sum_filter_add_sum_filter_not A (fun e : ℕ => (e : ℝ) ≤ Y)]
  have hlog2 : (1 : ℝ) / 2 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hLY : 0 < Real.log Y := Real.log_pos hY
  have hmemA : ∀ e ∈ A, e.Prime := fun e he => (Finset.mem_filter.1 he).2.1
  apply add_le_add
  · have h1 : ∀ e ∈ A.filter (fun e : ℕ => (e : ℝ) ≤ Y), 1 / Real.log e ≤ 2 := by
      intro e he
      have hp := hmemA e (Finset.mem_filter.1 he).1
      have he2 : (2 : ℝ) ≤ e := by exact_mod_cast hp.two_le
      have hl : Real.log 2 ≤ Real.log e := Real.log_le_log (by norm_num) he2
      rw [div_le_iff₀ (by linarith)]
      linarith
    have h2 := Finset.sum_le_card_nsmul _ _ _ h1
    rw [nsmul_eq_mul] at h2
    have hsub : A.filter (fun e : ℕ => (e : ℝ) ≤ Y) ⊆ Finset.Iic ⌊Y⌋₊ := by
      intro e he
      rw [Finset.mem_Iic]
      exact Nat.le_floor (Finset.mem_filter.1 he).2
    have hcard : ((A.filter (fun e : ℕ => (e : ℝ) ≤ Y)).card : ℝ) ≤ Y + 1 := by
      have h3 := Finset.card_le_card hsub
      rw [Nat.card_Iic] at h3
      have h4 : ((A.filter (fun e : ℕ => (e : ℝ) ≤ Y)).card : ℝ) ≤ ⌊Y⌋₊ + 1 := by
        exact_mod_cast h3
      have h5 : (⌊Y⌋₊ : ℝ) ≤ Y := Nat.floor_le (by linarith)
      linarith
    nlinarith
  · have h1 : ∀ e ∈ A.filter (fun e : ℕ => ¬ (e : ℝ) ≤ Y), 1 / Real.log e ≤ 1 / Real.log Y := by
      intro e he
      have hlt : Y < e := lt_of_not_ge (Finset.mem_filter.1 he).2
      exact one_div_le_one_div_of_le hLY (Real.log_le_log (by linarith) hlt.le)
    have h2 := Finset.sum_le_card_nsmul _ _ _ h1
    rw [nsmul_eq_mul] at h2
    have hcard : ((A.filter (fun e : ℕ => ¬ (e : ℝ) ≤ Y)).card : ℝ) ≤ A.card := by
      exact_mod_cast Finset.card_filter_le _ _
    calc _ ≤ ((A.filter (fun e : ℕ => ¬ (e : ℝ) ≤ Y)).card : ℝ) * (1 / Real.log Y) := h2
      _ ≤ (A.card : ℝ) * (1 / Real.log Y) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = (A.card : ℝ) / Real.log Y := mul_one_div _ _

end Principia.Erdos1054.Proofs.ClassMoment

namespace Principia.Erdos1054.Proofs

open Principia.Erdos1054.Proofs.ClassMoment
open Finset Filter
open scoped Topology

theorem link_Prop_ClassFirstMoment_tendsto : Spine.Link_Prop_ClassFirstMoment_tendsto := by
  intro hb Q hQ ρ
  obtain ⟨c, hc, A₀, hA⟩ := hb Q hQ ρ
  refine tendsto_atTop_mono' atTop ?_ ((tendsto_div_log_pow_atTop 2).const_mul_atTop hc)
  filter_upwards [eventually_ge_atTop A₀] with A hA'
  exact hA A hA'

theorem link_Coverage_Disp_MertensCoprimeQ : Spine.Link_Coverage_Disp_MertensCoprimeQ := by
  intro hM Q hQ
  have hφ : (0 : ℝ) < Q.totient := by exact_mod_cast Nat.totient_pos.2 (by omega)
  have hQR : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have h := (tendsto_const_nhds (x := (Q : ℝ) / Q.totient)).mul hM
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (Q : ℝ)] with y hy
  have hn : Q ≤ ⌊y⌋₊ := Nat.le_floor hy
  unfold Delta
  rw [prod_primes_split hQ hn]
  field_simp

theorem link_Coverage_Disp_ClassPrimeSum : Spine.Link_Coverage_Disp_ClassPrimeSum := by
  intro hPNT Q hQ
  have hφ : (0 : ℝ) < Q.totient := by exact_mod_cast Nat.totient_pos.2 (by omega)
  have hL := hPNT Q hQ
  have hLo : Tendsto (fun Z : ℝ => (piAP Z Q (Q - 1) : ℝ) * Real.log Z / Z * Q.totient) atTop
      (𝓝 1) := by
    have := hL.mul_const (Q.totient : ℝ)
    rwa [one_div, inv_mul_cancel₀ hφ.ne'] at this
  have h1 : Tendsto (fun Z : ℝ => Real.log (Real.log Z) / Real.log Z) atTop (𝓝 0) := by
    have := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp Real.tendsto_log_atTop
    refine this.congr' (Eventually.of_forall fun Z => ?_)
    simp
  have hlogratio : Tendsto (fun Z : ℝ => Real.log Z / Real.log (Z / Real.log Z ^ 3)) atTop
      (𝓝 1) := by
    have h2 : Tendsto (fun Z : ℝ => (1 - 3 * (Real.log (Real.log Z) / Real.log Z))⁻¹) atTop
        (𝓝 1) := by
      have := ((tendsto_const_nhds (x := (1 : ℝ))).sub (h1.const_mul 3)).inv₀ (by norm_num)
      simpa using this
    refine h2.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with Z hZ
    have hLpos : 0 < Real.log Z := Real.log_pos hZ
    have hL0 : Real.log Z ≠ 0 := hLpos.ne'
    have e1 : Real.log (Z / Real.log Z ^ 3) = Real.log Z - 3 * Real.log (Real.log Z) := by
      rw [Real.log_div (by linarith) (pow_ne_zero 3 hL0), Real.log_pow]
      push_cast
      ring
    have e2 : 1 - 3 * (Real.log (Real.log Z) / Real.log Z) =
        (Real.log Z - 3 * Real.log (Real.log Z)) / Real.log Z := by
      rw [sub_div, div_self hL0, mul_div_assoc]
    rw [e1, e2, inv_div]
  have t1 : Tendsto (fun Z : ℝ => 2 * (Q.totient : ℝ) / Real.log Z) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  have t2 : Tendsto (fun Z : ℝ => 2 * (Q.totient : ℝ) * (Real.log Z ^ 2 / Z)) atTop
      (𝓝 (2 * (Q.totient : ℝ) * 0)) := by
    have : Tendsto (fun Z : ℝ => Real.log Z ^ 2 / Z) atTop (𝓝 0) := by
      simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero
    exact this.const_mul _
  have hUp := (t1.add t2).add (hLo.mul hlogratio)
  rw [show (0 : ℝ) + 2 * (Q.totient : ℝ) * 0 + 1 * 1 = 1 by ring] at hUp
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hLo hUp ?_ ?_
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with Z hZ
    have hLpos : 0 < Real.log Z := Real.log_pos hZ
    have hZ0 : 0 < Z := by linarith
    have hlow := primeSum_lower Q hZ
    have hk : 0 ≤ (Q.totient : ℝ) * Real.log Z ^ 2 / Z := by positivity
    have e3 : (piAP Z Q (Q - 1) : ℝ) * Real.log Z / Z * Q.totient =
        (piAP Z Q (Q - 1) : ℝ) / Real.log Z * ((Q.totient : ℝ) * Real.log Z ^ 2 / Z) := by
      field_simp
    rw [e3, div_div_eq_mul_div]
    exact le_of_le_of_eq (mul_le_mul_of_nonneg_right hlow hk) (mul_div_assoc _ _ _).symm
  · filter_upwards [eventually_gt_atTop (1 : ℝ),
      (tendsto_div_log_pow_atTop 3).eventually_gt_atTop 1] with Z hZ hY
    have hLpos : 0 < Real.log Z := Real.log_pos hZ
    have hZ0 : 0 < Z := by linarith
    have hLY : 0 < Real.log (Z / Real.log Z ^ 3) := Real.log_pos hY
    have hup := primeSum_upper Q Z hY
    have hk : 0 ≤ (Q.totient : ℝ) * Real.log Z ^ 2 / Z := by positivity
    rw [div_div_eq_mul_div, mul_div_assoc]
    refine (mul_le_mul_of_nonneg_right hup hk).trans (le_of_eq ?_)
    field_simp

end Principia.Erdos1054.Proofs

namespace Principia.Erdos1054.Proofs.ClassMoment

open Finset Filter
open scoped Topology

/-- The primes `≤ e` not dividing `Q`. -/
def PQ (Q e : ℕ) : Finset ℕ := (Finset.range (e + 1)).filter (fun p : ℕ => p.Prime ∧ ¬ p ∣ Q)

/-- `P₀ = ∏_{p ≤ e, p ∤ Q} p`. -/
def P0 (Q e : ℕ) : ℕ := ∏ p ∈ PQ Q e, p

theorem mem_PQ {Q e p : ℕ} : p ∈ PQ Q e ↔ p ≤ e ∧ p.Prime ∧ ¬ p ∣ Q := by
  unfold PQ
  rw [Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]

theorem P0_pos (Q e : ℕ) : 0 < P0 Q e :=
  Finset.prod_pos (fun _ hp => (mem_PQ.1 hp).2.1.pos)

theorem P0_primeFactors (Q e : ℕ) : (P0 Q e).primeFactors = PQ Q e :=
  Nat.primeFactors_prod (fun _ hp => (mem_PQ.1 hp).2.1)

theorem P0_dvd_primorial (Q e : ℕ) : P0 Q e ∣ primorial e := by
  unfold P0 primorial
  apply Finset.prod_dvd_prod_of_subset
  intro p hp
  rw [mem_PQ] at hp
  rw [Finset.mem_filter, Finset.mem_range]
  exact ⟨by omega, hp.2.1⟩

theorem coprime_Q_P0 (Q e : ℕ) : Nat.Coprime Q (P0 Q e) := by
  unfold P0
  apply Nat.Coprime.prod_right
  intro p hp
  rw [mem_PQ] at hp
  exact ((Nat.Prime.coprime_iff_not_dvd hp.2.1).2 hp.2.2).symm

theorem totient_P0_div (Q e : ℕ) :
    ((P0 Q e).totient : ℝ) / (P0 Q e) = ∏ p ∈ PQ Q e, (1 - 1 / (p : ℝ)) := by
  rw [← prod_primeFactors_one_sub (P0_pos Q e), P0_primeFactors]

theorem coprime_mod_iff (x P : ℕ) : Nat.Coprime (x % P) P ↔ Nat.Coprime x P := by
  unfold Nat.Coprime
  rw [← Nat.gcd_rec, Nat.gcd_comm]

/-- **Counting coprime residues in a progression.** In a complete period `M P` (`M, P` coprime),
exactly `φ(P)` integers lie in a fixed class mod `M` and are coprime to `P`. -/
theorem card_ap_coprime {M P : ℕ} (hM : 0 < M) (hP : 0 < P) (hMP : Nat.Coprime M P) (c : ℕ) :
    ((Finset.range (M * P)).filter (fun a => a % M = c % M ∧ Nat.Coprime a P)).card =
      P.totient := by
  set c0 := c % M with hc0
  have hc0M : c0 < M := Nat.mod_lt c hM
  have hA : ((Finset.range (M * P)).filter (fun a => a % M = c0 ∧ Nat.Coprime a P)).card =
      ((Finset.range P).filter (fun k => Nat.Coprime (c0 + M * k) P)).card := by
    symm
    apply Finset.card_nbij' (fun k => c0 + M * k) (fun a => a / M)
    · intro k hk
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hk ⊢
      refine ⟨?_, ?_, hk.2⟩
      · have h1 : k + 1 ≤ P := hk.1
        have h2 : M * (k + 1) ≤ M * P := Nat.mul_le_mul_left M h1
        rw [Nat.mul_succ] at h2
        omega
      · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc0M]
    · intro a ha
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at ha ⊢
      refine ⟨Nat.div_lt_of_lt_mul ha.1, ?_⟩
      have h1 := Nat.mod_add_div a M
      rw [ha.2.1] at h1
      rw [h1]
      exact ha.2.2
    · intro k _
      simp only
      rw [Nat.add_mul_div_left _ _ hM, Nat.div_eq_of_lt hc0M, zero_add]
    · intro a ha
      rw [Finset.mem_coe, Finset.mem_filter] at ha
      have h1 := Nat.mod_add_div a M
      rw [ha.2.1] at h1
      exact h1
  rw [hA]
  set f : ℕ → ℕ := fun k => (c0 + M * k) % P with hf
  have hinj : Set.InjOn f (Finset.range P : Set ℕ) := by
    intro k1 hk1 k2 hk2 heq
    rw [Finset.mem_coe, Finset.mem_range] at hk1 hk2
    have h1 : c0 + M * k1 ≡ c0 + M * k2 [MOD P] := heq
    have h2 := Nat.ModEq.add_left_cancel' c0 h1
    have h3 : k1 ≡ k2 [MOD P] := Nat.ModEq.cancel_left_of_coprime (by
      rw [Nat.gcd_comm]; exact hMP) h2
    exact Nat.ModEq.eq_of_lt_of_lt h3 hk1 hk2
  have himage : (Finset.range P).image f = Finset.range P := by
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      rw [Finset.mem_image] at hy
      obtain ⟨k, -, rfl⟩ := hy
      rw [Finset.mem_range]
      exact Nat.mod_lt _ hP
    · rw [Finset.card_image_of_injOn hinj]
  have htot : P.totient = ((Finset.range P).filter (fun y => Nat.Coprime y P)).card := by
    unfold Nat.totient
    congr 1
    apply Finset.filter_congr
    intro y _
    exact Nat.coprime_comm
  calc ((Finset.range P).filter (fun k => Nat.Coprime (c0 + M * k) P)).card
      = ((Finset.range P).filter (fun k => Nat.Coprime (f k) P)).card := by
        congr 1
        apply Finset.filter_congr
        intro k _
        exact (coprime_mod_iff _ _).symm
    _ = (((Finset.range P).filter (fun k => Nat.Coprime (f k) P)).image f).card :=
        (Finset.card_image_of_injOn (hinj.mono
          (fun x hx => Finset.mem_coe.2 (Finset.mem_filter.1 (Finset.mem_coe.1 hx)).1))).symm
    _ = (((Finset.range P).image f).filter (fun y => Nat.Coprime y P)).card := by
        rw [Finset.filter_image]
    _ = ((Finset.range P).filter (fun y => Nat.Coprime y P)).card := by rw [himage]
    _ = P.totient := htot.symm

/-- Under the context, `𝒮_e` is `{t : t ≡ u (Q), gcd(t, P₀) = 1}`. -/
theorem mem_Se_iff {Q ρ h u e : ℕ} (hc : Coverage.ClassCtx Q ρ h u e) (t : ℕ) :
    t ∈ Coverage.Se Q u e ↔ t % Q = u % Q ∧ Nat.Coprime t (P0 Q e) := by
  have hep : e.Prime := hc.2.2.2.2.2.1
  have heQ := ctx_e_gt_Q hc
  have hQ : 1 ≤ Q := hc.1
  have hu : Nat.Coprime u Q := hc.2.2.2.1
  constructor
  · rintro ⟨-, htu, hcop⟩
    rw [primorialR_natCast] at hcop
    exact ⟨htu, Nat.Coprime.coprime_dvd_right (P0_dvd_primorial Q e) hcop⟩
  · rintro ⟨htu, hcop⟩
    have heP0 : e ∣ P0 Q e := by
      unfold P0
      apply Finset.dvd_prod_of_mem
      rw [mem_PQ]
      refine ⟨le_rfl, hep, fun hd => ?_⟩
      have := Nat.le_of_dvd (by omega) hd
      omega
    refine ⟨?_, htu, ?_⟩
    · by_contra h0
      have ht0 : t = 0 := by omega
      rw [ht0, Nat.coprime_zero_left] at hcop
      rw [hcop] at heP0
      exact hep.one_lt.ne' (Nat.dvd_one.1 heP0)
    · rw [primorialR_natCast]
      apply Nat.coprime_of_dvd
      intro p hp hpt hpprim
      have hpe : p ≤ e := (Nat.Prime.dvd_primorial_iff hp).1 hpprim
      by_cases hpQ : p ∣ Q
      · have htu' : t ≡ u [MOD p] := Nat.ModEq.of_dvd hpQ htu
        have hu0 : u % p = 0 := by
          rw [← htu']
          exact Nat.mod_eq_zero_of_dvd hpt
        have hpu : p ∣ u := Nat.dvd_of_mod_eq_zero hu0
        have h1 : p ∣ Nat.gcd u Q := Nat.dvd_gcd hpu hpQ
        rw [hu] at h1
        exact hp.one_lt.ne' (Nat.dvd_one.1 h1)
      · have hpP0 : p ∣ P0 Q e := by
          unfold P0
          apply Finset.dvd_prod_of_mem
          rw [mem_PQ]
          exact ⟨hpe, hp, hpQ⟩
        have h1 : p ∣ Nat.gcd t (P0 Q e) := Nat.dvd_gcd hpt hpP0
        rw [hcop] at h1
        exact hp.one_lt.ne' (Nat.dvd_one.1 h1)

theorem deltaE_eq (Q e : ℕ) :
    Coverage.deltaE Q e = ((P0 Q e).totient : ℝ) / ((Q * P0 Q e : ℕ) : ℝ) := by
  unfold Coverage.deltaE
  have h := totient_P0_div Q e
  unfold PQ at h
  rw [← h]
  push_cast
  have hP : (P0 Q e : ℝ) ≠ 0 := by exact_mod_cast (P0_pos Q e).ne'
  field_simp

theorem exists_inv_mod {a Q : ℕ} (hQ : 0 < Q) (h : Nat.Coprime a Q) :
    ∃ a' : ℕ, (a : ZMod Q) * (a' : ZMod Q) = 1 := by
  haveI : NeZero Q := ⟨hQ.ne'⟩
  refine ⟨(((ZMod.unitOfCoprime a h)⁻¹ : (ZMod Q)ˣ) : ZMod Q).val, ?_⟩
  rw [ZMod.natCast_zmod_val, ← ZMod.coe_unitOfCoprime a h, Units.mul_inv]

/-- `hasDens_of_mem_iff_mod_mem` with the count taken over an explicit decidable predicate
(avoids the classical-instance mismatch of the density toolkit's `filter (· ∈ S)`). -/
theorem hasDens_of_mod_count {S : Set ℕ} {M : ℕ} (hM : 0 < M) (hS : ∀ N, N ∈ S ↔ N % M ∈ S)
    {p : ℕ → Prop} [DecidablePred p] (hp : ∀ x, x ∈ S ↔ p x) :
    HasDens S (((Finset.range M).filter p).card / M) := by
  classical
  have h := hasDens_of_mem_iff_mod_mem hM hS
  rwa [Finset.filter_congr (fun x _ => hp x)] at h

end Principia.Erdos1054.Proofs.ClassMoment

namespace Principia.Erdos1054.Proofs

open Principia.Erdos1054.Proofs.ClassMoment
open Finset Filter
open scoped Topology

open Classical in
theorem leaf_Coverage_Step_SeDensity : Coverage.Step_SeDensity := by
  intro Q ρ h u e hc
  have hQ : 1 ≤ Q := hc.1
  refine ⟨?_, ?_⟩
  · have hM : 0 < Q * P0 Q e := Nat.mul_pos (by omega) (P0_pos Q e)
    have hS : ∀ N, N ∈ Coverage.Se Q u e ↔ N % (Q * P0 Q e) ∈ Coverage.Se Q u e := by
      intro N
      rw [mem_Se_iff hc, mem_Se_iff hc, Nat.mod_mod_of_dvd N (Dvd.intro _ rfl)]
      have hmod : N % (Q * P0 Q e) ≡ N [MOD P0 Q e] :=
        (Nat.mod_modEq N (Q * P0 Q e)).of_dvd (Dvd.intro_left _ rfl)
      unfold Nat.Coprime
      rw [hmod.gcd_eq]
    have hd := hasDens_of_mem_iff_mod_mem hM hS
    have hcard : ((Finset.range (Q * P0 Q e)).filter (· ∈ Coverage.Se Q u e)).card =
        (P0 Q e).totient := by
      rw [← card_ap_coprime (M := Q) (P := P0 Q e) (by omega) (P0_pos Q e) (coprime_Q_P0 Q e) u]
      congr 1
      apply Finset.filter_congr
      intro x _
      exact mem_Se_iff hc x
    rw [hcard] at hd
    rw [deltaE_eq]
    exact hd
  · intro t ht p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpt : p ∣ t := Nat.dvd_of_mem_primeFactors hp
    by_contra hle
    have hle' : p ≤ e := by
      have : (p : ℝ) ≤ e := le_of_not_gt hle
      exact_mod_cast this
    have hcop := ht.2.2
    rw [primorialR_natCast] at hcop
    have h1 : p ∣ Nat.gcd t (primorial e) :=
      Nat.dvd_gcd hpt ((Nat.Prime.dvd_primorial_iff hpp).2 hle')
    rw [hcop] at h1
    exact hpp.one_lt.ne' (Nat.dvd_one.1 h1)

theorem leaf_Coverage_Step_SeMultiplesDens : Coverage.Step_SeMultiplesDens := by
  intro Q ρ h u e hc a ha hacop
  have hQ : 1 ≤ Q := hc.1
  have heQ := ctx_e_gt_Q hc
  rw [primorialR_natCast] at hacop
  have haQ : Nat.Coprime a Q := by
    apply Nat.coprime_of_dvd
    intro p hp hpa hpQ
    have hpe : p ≤ e := (Nat.le_of_dvd (by omega) hpQ).trans heQ.le
    have h1 : p ∣ Nat.gcd a (primorial e) :=
      Nat.dvd_gcd hpa ((Nat.Prime.dvd_primorial_iff hp).2 hpe)
    rw [hacop] at h1
    exact hp.one_lt.ne' (Nat.dvd_one.1 h1)
  have haP : Nat.Coprime a (P0 Q e) := Nat.Coprime.coprime_dvd_right (P0_dvd_primorial Q e) hacop
  obtain ⟨a', ha'⟩ := exists_inv_mod (by omega : 0 < Q) haQ
  have hkey : ∀ s : ℕ, (a * s) % Q = u % Q ↔ s % Q = (a' * u) % Q := by
    intro s
    rw [← ZMod.natCast_eq_natCast_iff', ← ZMod.natCast_eq_natCast_iff']
    push_cast
    constructor
    · intro h1
      linear_combination (-(s : ZMod Q)) * ha' + (a' : ZMod Q) * h1
    · intro h1
      linear_combination (u : ZMod Q) * ha' + (a : ZMod Q) * h1
  have hM : 0 < a * (Q * P0 Q e) := Nat.mul_pos (by omega) (Nat.mul_pos (by omega) (P0_pos Q e))
  have hmemT : ∀ N, N ∈ {t : ℕ | t ∈ Coverage.Se Q u e ∧ a ∣ t} ↔
      ((N % Q = u % Q ∧ Nat.Coprime N (P0 Q e)) ∧ a ∣ N) := by
    intro N
    rw [Set.mem_setOf_eq, mem_Se_iff hc]
  have hS : ∀ N, N ∈ {t : ℕ | t ∈ Coverage.Se Q u e ∧ a ∣ t} ↔
      N % (a * (Q * P0 Q e)) ∈ {t : ℕ | t ∈ Coverage.Se Q u e ∧ a ∣ t} := by
    intro N
    rw [hmemT, hmemT, Nat.mod_mod_of_dvd N (Dvd.dvd.mul_left (Dvd.intro _ rfl) a),
      Nat.dvd_mod_iff (Dvd.intro _ rfl)]
    have hmod : N % (a * (Q * P0 Q e)) ≡ N [MOD P0 Q e] :=
      (Nat.mod_modEq N _).of_dvd (Dvd.dvd.mul_left (Dvd.intro_left _ rfl) a)
    unfold Nat.Coprime
    rw [hmod.gcd_eq]
  have hd := hasDens_of_mod_count hM hS hmemT
  have hcard : ((Finset.range (a * (Q * P0 Q e))).filter
      (fun N => (N % Q = u % Q ∧ Nat.Coprime N (P0 Q e)) ∧ a ∣ N)).card = (P0 Q e).totient := by
    rw [← card_ap_coprime (M := Q) (P := P0 Q e) (by omega) (P0_pos Q e) (coprime_Q_P0 Q e)
      (a' * u)]
    symm
    apply Finset.card_nbij' (fun s => a * s) (fun r => r / a)
    · intro s hs
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hs ⊢
      exact ⟨Nat.mul_lt_mul_of_pos_left hs.1 (by omega),
        ⟨(hkey s).2 hs.2.1, Nat.coprime_mul_iff_left.2 ⟨haP, hs.2.2⟩⟩, dvd_mul_right a s⟩
    · intro r hr
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hr ⊢
      obtain ⟨hr1, ⟨hr2, hr3⟩, hr4⟩ := hr
      have hr5 : a * (r / a) = r := Nat.mul_div_cancel' hr4
      refine ⟨Nat.div_lt_of_lt_mul hr1, ?_, ?_⟩
      · apply (hkey (r / a)).1
        rw [hr5]
        exact hr2
      · rw [← hr5] at hr3
        exact (Nat.coprime_mul_iff_left.1 hr3).2
    · intro s _
      exact Nat.mul_div_cancel_left s (by omega)
    · intro r hr
      simp only [Finset.mem_coe, Finset.mem_filter] at hr
      exact Nat.mul_div_cancel' hr.2.2
  rw [hcard] at hd
  have hval : Coverage.deltaE Q e / a = ((P0 Q e).totient : ℝ) / ((a * (Q * P0 Q e) : ℕ) : ℝ) := by
    rw [deltaE_eq]
    push_cast
    have haR : (a : ℝ) ≠ 0 := by exact_mod_cast (show a ≠ 0 by omega)
    have hQR : (Q : ℝ) ≠ 0 := by exact_mod_cast (show Q ≠ 0 by omega)
    have hP : (P0 Q e : ℝ) ≠ 0 := by exact_mod_cast (P0_pos Q e).ne'
    field_simp
  rw [hval]
  exact hd

end Principia.Erdos1054.Proofs

namespace Principia.Erdos1054.Proofs.ClassMoment

open Finset Filter
open scoped Topology

theorem deltaE_nonneg (Q e : ℕ) : 0 ≤ Coverage.deltaE Q e := by
  unfold Coverage.deltaE
  apply mul_nonneg (by positivity)
  apply Finset.prod_nonneg
  intro p hp
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Finset.mem_filter.1 hp).2.1.two_le
  rw [sub_nonneg, div_le_one (by linarith)]
  linarith

theorem coprimeSq_le (e a : ℕ) : Coverage.coprimeSq e a ≤ 1 / (a : ℝ) ^ 2 := by
  unfold Coverage.coprimeSq
  split_ifs
  · exact le_rfl
  · positivity

theorem coprimeSq_nonneg (e a : ℕ) : 0 ≤ Coverage.coprimeSq e a := by
  unfold Coverage.coprimeSq
  split_ifs
  · positivity
  · exact le_rfl

theorem summable_coprimeSq (e : ℕ) : Summable (Coverage.coprimeSq e) :=
  Summable.of_nonneg_of_le (coprimeSq_nonneg e) (coprimeSq_le e)
    (Real.summable_one_div_nat_pow.2 one_lt_two)

/-- The `a`-th term of the divisor-swapped mean. -/
noncomputable def fT (Q u e : ℕ) (T a : ℕ) : ℝ :=
  if 1 < a then (1 / (a : ℝ)) * ((cnt {t : ℕ | t ∈ Coverage.Se Q u e ∧ a ∣ t} T : ℝ) / T)
  else 0

theorem cnt_mult_eq_zero_of_lt {Q u e T a : ℕ} (haT : T < a) :
    cnt {t : ℕ | t ∈ Coverage.Se Q u e ∧ a ∣ t} T = 0 := by
  rw [cnt_natCast, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro t ht
  rw [mem_cntFinset] at ht
  obtain ⟨⟨ht1, htT⟩, hmem⟩ := ht
  have hat : a ∣ t := hmem.2
  have := Nat.le_of_dvd (by omega) hat
  omega

theorem fT_nonneg (Q u e T a : ℕ) : 0 ≤ fT Q u e T a := by
  unfold fT
  split_ifs
  · positivity
  · exact le_rfl

theorem fT_le (Q u e T a : ℕ) : fT Q u e T a ≤ 1 / (a : ℝ) ^ 2 := by
  unfold fT
  split_ifs with ha
  · have haR : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
    rcases Nat.eq_zero_or_pos T with hT | hT
    · subst hT
      simp only [Nat.cast_zero, div_zero, mul_zero]
      positivity
    · have hTR : (0 : ℝ) < T := by exact_mod_cast hT
      have h1 : (cnt {t : ℕ | t ∈ Coverage.Se Q u e ∧ a ∣ t} T : ℝ) ≤ T / a := by
        have h2 := cnt_mono (show {t : ℕ | t ∈ Coverage.Se Q u e ∧ a ∣ t} ⊆ {N : ℕ | a ∣ N} from
          fun t ht => ht.2) (T : ℝ)
        have h3 := cnt_dvd_le a (Nat.cast_nonneg T : (0 : ℝ) ≤ T)
        exact (Nat.cast_le.2 h2).trans h3
      have h4 : (cnt {t : ℕ | t ∈ Coverage.Se Q u e ∧ a ∣ t} T : ℝ) / T ≤ 1 / a := by
        rw [div_le_iff₀ hTR]
        calc _ ≤ (T : ℝ) / a := h1
          _ = 1 / a * T := by ring
      calc 1 / (a : ℝ) * ((cnt {t : ℕ | t ∈ Coverage.Se Q u e ∧ a ∣ t} T : ℝ) / T)
          ≤ 1 / a * (1 / a) := mul_le_mul_of_nonneg_left h4 (by positivity)
        _ = 1 / (a : ℝ) ^ 2 := by ring
  · positivity

open Classical in
/-- The exact finite identity behind `Disp_HeMean`: the mean of `H_e(t)/t` over `𝒮_e ∩ [1,T]`
splits as the density term plus `(e+1)` times the divisor-swapped series. -/
theorem mean_identity (hRatio : Coverage.Step_HeRatio) {Q ρ h u e : ℕ}
    (hc : Coverage.ClassCtx Q ρ h u e) (T : ℕ) :
    (1 / (T : ℝ)) * ∑ t ∈ (Finset.Icc 1 T).filter (· ∈ Coverage.Se Q u e),
        (Coverage.He e t : ℝ) / t =
      (cnt (Coverage.Se Q u e) T : ℝ) / T + ((e : ℝ) + 1) * ∑' a : ℕ, fT Q u e T a := by
  set SeT := (Finset.Icc 1 T).filter (· ∈ Coverage.Se Q u e) with hSeT
  have h1 : ∑ t ∈ SeT, (Coverage.He e t : ℝ) / t =
      ∑ t ∈ SeT, (1 + ((e : ℝ) + 1) * ∑ a ∈ t.divisors.filter (1 < ·), 1 / (a : ℝ)) := by
    apply Finset.sum_congr rfl
    intro t ht
    exact hRatio Q ρ h u e hc t (Finset.mem_filter.1 ht).2
  have h2 : ∑ t ∈ SeT, ∑ a ∈ t.divisors.filter (1 < ·), 1 / (a : ℝ) =
      ∑ a ∈ (Finset.range (T + 1)).filter (1 < ·), ∑ t ∈ SeT.filter (a ∣ ·), 1 / (a : ℝ) := by
    apply Finset.sum_comm'
    intro t a
    simp only [hSeT, Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors, Finset.mem_range]
    constructor
    · rintro ⟨⟨⟨ht1, htT⟩, hS⟩, ⟨hat, -⟩, ha1⟩
      have := Nat.le_of_dvd (by omega) hat
      exact ⟨⟨⟨⟨ht1, htT⟩, hS⟩, hat⟩, by omega, ha1⟩
    · rintro ⟨⟨⟨⟨ht1, htT⟩, hS⟩, hat⟩, -, ha1⟩
      exact ⟨⟨⟨ht1, htT⟩, hS⟩, ⟨hat, by omega⟩, ha1⟩
  have hcnt : ∀ a : ℕ, (SeT.filter (a ∣ ·)).card =
      cnt {t : ℕ | t ∈ Coverage.Se Q u e ∧ a ∣ t} T := by
    intro a
    rw [cnt_natCast]
    congr 1
    ext x
    rw [mem_cntFinset, Finset.mem_filter, hSeT, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h2, h3⟩, fun ⟨h1, h2, h3⟩ => ⟨⟨h1, h2⟩, h3⟩⟩
  have h3 : ∑' a : ℕ, fT Q u e T a = ∑ a ∈ Finset.range (T + 1), fT Q u e T a := by
    apply tsum_eq_sum
    intro a ha
    rw [Finset.mem_range, not_lt] at ha
    unfold fT
    rw [cnt_mult_eq_zero_of_lt (show T < a by omega)]
    simp
  have h4 : ∑ a ∈ Finset.range (T + 1), fT Q u e T a =
      ∑ a ∈ (Finset.range (T + 1)).filter (1 < ·),
        (1 / (a : ℝ)) * ((cnt {t : ℕ | t ∈ Coverage.Se Q u e ∧ a ∣ t} T : ℝ) / T) := by
    rw [Finset.sum_filter]
    rfl
  have hcntSe : (cnt (Coverage.Se Q u e) T : ℝ) = SeT.card := by
    rw [cnt_natCast]
  rw [h3, h4, h1, Finset.sum_add_distrib, ← Finset.mul_sum, h2, hcntSe]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro a _
    rw [hcnt a]
    ring

end Principia.Erdos1054.Proofs.ClassMoment

namespace Principia.Erdos1054.Proofs

open Principia.Erdos1054.Proofs.ClassMoment
open Finset Filter
open scoped Topology

theorem link_Coverage_Disp_HeMean : Spine.Link_Coverage_Disp_HeMean := by
  intro hRatio hSe hMul hTail Q ρ h u e hc
  have hδ0 := deltaE_nonneg Q e
  obtain ⟨-, htail1, htail2, htail3⟩ := hTail Q ρ h u e hc
  refine ⟨summable_coprimeSq e, ?_, ?_⟩
  · have hdens := (hSe Q ρ h u e hc).1
    have hab : ∀ a : ℕ, Tendsto (fun T : ℕ => fT Q u e T a) atTop
        (𝓝 (Coverage.deltaE Q e * Coverage.coprimeSq e a)) := by
      intro a
      unfold fT Coverage.coprimeSq
      by_cases ha : 1 < a
      · by_cases hcop : Nat.Coprime a (primorialR e)
        · simp only [if_pos ha, if_pos (And.intro ha hcop)]
          have hm := (hMul Q ρ h u e hc a ha hcop).const_mul (1 / (a : ℝ))
          convert hm using 2
          ring
        · simp only [if_pos ha,
            if_neg (show ¬ (1 < a ∧ Nat.Coprime a (primorialR e)) from fun h => hcop h.2), mul_zero]
          have hempty : {t : ℕ | t ∈ Coverage.Se Q u e ∧ a ∣ t} = ∅ := by
            ext t
            simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
            intro ht hat
            exact hcop (Nat.Coprime.coprime_dvd_left hat ht.2.2)
          rw [hempty]
          simp [cnt_empty]
      · simp only [if_neg ha,
          if_neg (show ¬ (1 < a ∧ Nat.Coprime a (primorialR e)) from fun h => ha h.1), mul_zero]
        exact tendsto_const_nhds
    have hbound : ∀ᶠ T : ℕ in atTop, ∀ a : ℕ, ‖fT Q u e T a‖ ≤ 1 / (a : ℝ) ^ 2 :=
      Eventually.of_forall (fun T a => by
        rw [Real.norm_eq_abs, abs_of_nonneg (fT_nonneg Q u e T a)]
        exact fT_le Q u e T a)
    have htsum := tendsto_tsum_of_dominated_convergence
      (Real.summable_one_div_nat_pow.2 one_lt_two) hab hbound
    rw [tsum_mul_left] at htsum
    have hsum := hdens.add (htsum.const_mul ((e : ℝ) + 1))
    have hlim : Coverage.deltaE Q e +
        ((e : ℝ) + 1) * (Coverage.deltaE Q e * ∑' a : ℕ, Coverage.coprimeSq e a) =
        Coverage.deltaE Q e * (1 + ((e : ℝ) + 1) * ∑' a : ℕ, Coverage.coprimeSq e a) := by ring
    rw [hlim] at hsum
    refine hsum.congr' (Eventually.of_forall (fun T => ?_))
    exact (mean_identity hRatio hc T).symm
  · have hX : ((e : ℝ) + 1) * ∑' a : ℕ, Coverage.coprimeSq e a ≤ 3 / 2 :=
      htail1.trans (htail2.trans htail3)
    nlinarith

open Classical in
theorem link_Coverage_Step_GeLowerDens : Spine.Link_Coverage_Step_GeLowerDens := by
  intro hSe hMean Q ρ h u e hc
  have hdens := (hSe Q ρ h u e hc).1
  obtain ⟨-, hlim, hle⟩ := hMean Q ρ h u e hc
  set L := Coverage.deltaE Q e * (1 + ((e : ℝ) + 1) * ∑' a : ℕ, Coverage.coprimeSq e a) with hL
  set S : ℕ → ℝ := fun T => ∑ t ∈ (Finset.Icc 1 T).filter (· ∈ Coverage.Se Q u e),
    (Coverage.He e t : ℝ) / t with hS
  have hv : Tendsto (fun T : ℕ => (cnt (Coverage.Se Q u e) T : ℝ) / T - 1 / 6 * ((1 / (T : ℝ)) * S T))
      atTop (𝓝 (Coverage.deltaE Q e - 1 / 6 * L)) := hdens.sub (hlim.const_mul (1 / 6))
  have hS0 : ∀ T, 0 ≤ S T := fun T => Finset.sum_nonneg (fun t _ => by positivity)
  have hmark : ∀ T : ℕ, (cnt (Coverage.Se Q u e) T : ℝ) / T - 1 / 6 * ((1 / (T : ℝ)) * S T) ≤
      (cnt (Coverage.Ge Q u e) T : ℝ) / T := by
    intro T
    have hsd : (cnt (Coverage.Se Q u e \ Coverage.Ge Q u e) T : ℝ) ≤ 1 / 6 * S T := by
      rw [cnt_natCast, Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, hS, Finset.mul_sum]
      refine le_trans (Finset.sum_le_sum (fun t ht => ?_))
        (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun t _ _ => by positivity))
      · rw [mem_cntFinset] at ht
        obtain ⟨⟨ht1, -⟩, hSe', hGe'⟩ := ht
        have hgt : 6 * t < Coverage.He e t := by
          by_contra hcon
          exact hGe' ⟨hSe', not_lt.1 hcon⟩
        have htR : (0 : ℝ) < t := by exact_mod_cast ht1
        have hgtR : 6 * (t : ℝ) < Coverage.He e t := by exact_mod_cast hgt
        have h6 : (6 : ℝ) ≤ (Coverage.He e t : ℝ) / t := by
          rw [le_div_iff₀ htR]
          linarith
        linarith
      · intro t ht
        rw [mem_cntFinset] at ht ⊢
        exact ⟨ht.1, ht.2.1⟩
    have hsplit : (cnt (Coverage.Se Q u e) T : ℝ) ≤
        (cnt (Coverage.Se Q u e \ Coverage.Ge Q u e) T : ℝ) + cnt (Coverage.Ge Q u e) T := by
      exact_mod_cast cnt_le_cnt_sdiff_add _ _ _
    have hkey : (cnt (Coverage.Se Q u e) T : ℝ) - 1 / 6 * S T ≤ cnt (Coverage.Ge Q u e) T := by
      linarith
    rcases Nat.eq_zero_or_pos T with hT | hT
    · subst hT
      simp
    · have hTR : (0 : ℝ) < T := by exact_mod_cast hT
      have e1 : (cnt (Coverage.Se Q u e) T : ℝ) / T - 1 / 6 * ((1 / (T : ℝ)) * S T) =
          ((cnt (Coverage.Se Q u e) T : ℝ) - 1 / 6 * S T) / T := by
        field_simp
      rw [e1]
      exact div_le_div_of_nonneg_right hkey hTR.le
  have hlow : Coverage.deltaE Q e - 1 / 6 * L ≤ lowerDens (Coverage.Ge Q u e) := by
    unfold lowerDens
    rw [← hv.liminf_eq]
    exact liminf_le_liminf (Eventually.of_forall hmark) hv.isBoundedUnder_ge
      (isCoboundedUnder_ge_cnt_div _)
  linarith

end Principia.Erdos1054.Proofs

namespace Principia.Erdos1054.Proofs.ClassMoment

open Finset Filter
open scoped Topology

/-- **Upper bound on the pair count** (the boundedness that makes `lamLower` a genuine liminf):
for `A X ≥ 1`, `∑_{N ≤ X} r_A(N) ≤ X + A² · C₂ A X`. Pairs with `e = 1` inject into `[1, X]`
(`d ≤ F_1(d) = N`); pairs with `e ≥ 2` have weight `(A g_e(ed))² ≥ 1` by `eq:reflection` and inject
into the index set of `eq:moment` (`k = 2`, `E = 1`, `Z = A X`). -/
theorem sum_rt_le (hRefl : Eq_Reflection) {A : ℝ} (hA : 0 < A) {C2 : ℝ} (hmom : Eq_Moment 2 C2)
    (X : ℕ) (hAX : 1 ≤ A * X) :
    ∑ N ∈ Finset.Icc 1 X, (rt A N : ℝ) ≤ X + A ^ 2 * (C2 * (A * X)) := by
  classical
  set box : ℕ → Finset (ℕ × ℕ) := fun N =>
    (((Finset.Icc 1 ⌊A * N⌋₊) ×ˢ (Finset.Icc 1 ⌊A * N⌋₊)).filter
      (fun p => F p.1 p.2 = N ∧ ((p.1 * p.2 : ℕ) : ℝ) ≤ A * N)) with hbox
  have hrt : ∀ N, rt A N = (box N).card := by
    intro N
    unfold rt
    rw [hbox]
  set Sg := (Finset.Icc 1 X).sigma box with hSg
  have hsum : ∑ N ∈ Finset.Icc 1 X, (rt A N : ℝ) = (Sg.card : ℝ) := by
    rw [hSg, Finset.card_sigma]
    push_cast
    exact Finset.sum_congr rfl (fun N _ => by rw [hrt])
  have hmemSg : ∀ x : (Σ _ : ℕ, ℕ × ℕ), x ∈ Sg ↔
      (1 ≤ x.1 ∧ x.1 ≤ X) ∧ ((1 ≤ x.2.1 ∧ x.2.1 ≤ ⌊A * x.1⌋₊) ∧
        (1 ≤ x.2.2 ∧ x.2.2 ≤ ⌊A * x.1⌋₊)) ∧
        F x.2.1 x.2.2 = x.1 ∧ ((x.2.1 * x.2.2 : ℕ) : ℝ) ≤ A * x.1 := by
    intro x
    rw [hSg, Finset.mem_sigma, Finset.mem_Icc, hbox]
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  rw [hsum, ← Finset.card_filter_add_card_filter_not (s := Sg) (fun x => x.2.1 = 1)]
  push_cast
  apply add_le_add
  · -- the pairs with `e = 1`
    have h1 : (Sg.filter (fun x => x.2.1 = 1)).card ≤ (Finset.Icc 1 X).card := by
      apply Finset.card_le_card_of_injOn (fun x => x.2.2)
      · intro x hx
        rw [Finset.mem_coe, Finset.mem_filter, hmemSg] at hx
        obtain ⟨⟨⟨hN1, hNX⟩, ⟨-, hd1⟩, hF, -⟩, he1⟩ := hx
        rw [Finset.mem_coe, Finset.mem_Icc]
        refine ⟨hd1.1, ?_⟩
        show x.2.2 ≤ X
        have := F_ge x.2.1 x.2.2 (by omega) hd1.1
        omega
      · rintro ⟨N1, e1, d1⟩ hx ⟨N2, e2, d2⟩ hy heq
        rw [Finset.mem_coe, Finset.mem_filter, hmemSg] at hx hy
        simp only at heq hx hy
        obtain ⟨-, -, hF1, -⟩ := hx.1
        obtain ⟨-, -, hF2, -⟩ := hy.1
        have he : e1 = e2 := by rw [hx.2, hy.2]
        subst he heq
        rw [← hF1, ← hF2]
    rw [Nat.card_Icc, Nat.add_sub_cancel] at h1
    exact_mod_cast h1
  · -- the pairs with `e ≥ 2`, via `eq:moment`
    set s := Sg.filter (fun x => ¬ x.2.1 = 1) with hs
    have hw : ∀ x ∈ s, (1 : ℝ) ≤ (A * g x.2.1 (x.2.1 * x.2.2)) ^ 2 := by
      intro x hx
      rw [hs, Finset.mem_filter, hmemSg] at hx
      obtain ⟨⟨⟨hN1, -⟩, ⟨he1, hd1⟩, hF, hle⟩, -⟩ := hx
      have hr := hRefl x.2.1 x.2.2 he1.1 hd1.1
      rw [hF] at hr
      have hed : (0 : ℝ) < (x.2.1 : ℝ) * x.2.2 := by
        have : (1 : ℝ) ≤ x.2.1 := by exact_mod_cast he1.1
        have : (1 : ℝ) ≤ x.2.2 := by exact_mod_cast hd1.1
        positivity
      have hle' : (x.2.1 : ℝ) * x.2.2 ≤ A * x.1 := by exact_mod_cast hle
      have h1 : (1 : ℝ) ≤ A * g x.2.1 (x.2.1 * x.2.2) := by
        have h2 : (x.2.1 : ℝ) * x.2.2 * 1 ≤ (x.2.1 : ℝ) * x.2.2 * (A * g x.2.1 (x.2.1 * x.2.2)) := by
          have : (x.2.1 : ℝ) * x.2.2 * (A * g x.2.1 (x.2.1 * x.2.2)) = A * x.1 := by
            rw [hr]
            ring
          rw [this]
          linarith
        exact le_of_mul_le_mul_left h2 hed
      exact one_le_pow₀ h1
    have hcard : (s.card : ℝ) ≤ ∑ x ∈ s, (A * g x.2.1 (x.2.1 * x.2.2)) ^ 2 := by
      rw [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
      exact Finset.sum_le_sum hw
    have hpull : ∑ x ∈ s, (A * g x.2.1 (x.2.1 * x.2.2)) ^ 2 =
        A ^ 2 * ∑ x ∈ s, g x.2.1 (x.2.1 * x.2.2) ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun x _ => by ring)
    set T := (Finset.Icc 1 ⌊A * X⌋₊).sigma
      (fun n : ℕ => n.divisors.filter (fun e : ℕ => (1 : ℝ) < (e : ℝ))) with hT
    have hmomT : momentSum 2 1 (A * X) = ∑ y ∈ T, g y.2 y.1 ^ 2 := by
      unfold momentSum
      rw [hT, Finset.sum_sigma]
    have hinj : Set.InjOn (fun x : (Σ _ : ℕ, ℕ × ℕ) => (⟨x.2.1 * x.2.2, x.2.1⟩ : Σ _ : ℕ, ℕ))
        (s : Set (Σ _ : ℕ, ℕ × ℕ)) := by
      rintro ⟨N1, e1, d1⟩ hx ⟨N2, e2, d2⟩ hy heq
      rw [Finset.mem_coe, hs, Finset.mem_filter, hmemSg] at hx hy
      simp only [Sigma.mk.inj_iff, heq_eq_eq] at heq hx hy
      obtain ⟨hn, he⟩ := heq
      subst he
      have hd : d1 = d2 := Nat.eq_of_mul_eq_mul_left (by omega) hn
      subst hd
      obtain ⟨-, -, hF1, -⟩ := hx.1
      obtain ⟨-, -, hF2, -⟩ := hy.1
      rw [← hF1, ← hF2]
    have hmaps : ∀ x ∈ s, (⟨x.2.1 * x.2.2, x.2.1⟩ : Σ _ : ℕ, ℕ) ∈ T := by
      intro x hx
      rw [hs, Finset.mem_filter, hmemSg] at hx
      obtain ⟨⟨⟨hN1, hNX⟩, ⟨he1, hd1⟩, hF, hle⟩, hne⟩ := hx
      rw [hT, Finset.mem_sigma, Finset.mem_Icc, Finset.mem_filter, Nat.mem_divisors]
      have hpos : 1 ≤ x.2.1 * x.2.2 := Nat.one_le_iff_ne_zero.2
        (Nat.mul_ne_zero (by omega) (by omega))
      refine ⟨⟨hpos, ?_⟩, ⟨dvd_mul_right _ _, Nat.one_le_iff_ne_zero.1 hpos⟩, ?_⟩
      · apply Nat.le_floor
        have hNXR : (x.1 : ℝ) ≤ X := by exact_mod_cast hNX
        calc ((x.2.1 * x.2.2 : ℕ) : ℝ) ≤ A * x.1 := hle
          _ ≤ A * X := mul_le_mul_of_nonneg_left hNXR hA.le
      · have : 2 ≤ x.2.1 := by omega
        exact_mod_cast this
    have hsub : ∑ x ∈ s, g x.2.1 (x.2.1 * x.2.2) ^ 2 ≤ ∑ y ∈ T, g y.2 y.1 ^ 2 := by
      rw [← Finset.sum_image (f := fun y : (Σ _ : ℕ, ℕ) => g y.2 y.1 ^ 2) hinj]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro y hy
        rw [Finset.mem_image] at hy
        obtain ⟨x, hx, rfl⟩ := hy
        exact hmaps x hx
      · intro y _ _
        positivity
    have hm := hmom 1 (A * X) le_rfl hAX
    rw [Real.one_rpow, mul_one] at hm
    calc (s.card : ℝ) ≤ A ^ 2 * ∑ x ∈ s, g x.2.1 (x.2.1 * x.2.2) ^ 2 := hpull ▸ hcard
      _ ≤ A ^ 2 * momentSum 2 1 (A * X) := by
          rw [hmomT]
          exact mul_le_mul_of_nonneg_left hsub (by positivity)
      _ ≤ A ^ 2 * (C2 * (A * X)) := mul_le_mul_of_nonneg_left hm (by positivity)

open Classical in
/-- **The injection of `eq:class-lower`**: each `(e, t)` with `e` eligible, `t ∈ 𝒢_e`,
`t ≤ X/(6σ(h))` gives the pair `(e, h t)` counted by `r_A(F_e(ht))`, with `F_e(ht) ≤ X` in the
class `ρ`. Distinct `(e, t)` give distinct pairs `(e, ht)`. -/
theorem lower_count (hHe : Eq_He) (hCR : Coverage.Step_ClassResidue)
    (hRR : Eq_RepresentingRatio) {Q ρ h u : ℕ} {A : ℝ} (E : Finset ℕ)
    (hctx : ∀ e ∈ E, Coverage.ClassCtx Q ρ h u e) (heA : ∀ e ∈ E, (e : ℝ) * h ≤ A) (X : ℕ) :
    ∑ e ∈ E, (cnt (Coverage.Ge Q u e) ((X : ℝ) / (6 * sig h)) : ℝ) ≤
      ∑ N ∈ (Finset.Icc 1 X).filter (fun N : ℕ => N % Q = ρ % Q), (rt A N : ℝ) := by
  set σ : ℝ := (sig h : ℝ) with hσdef
  set M := ⌊(X : ℝ) / (6 * σ)⌋₊ with hM
  set box : ℕ → Finset (ℕ × ℕ) := fun N =>
    (((Finset.Icc 1 ⌊A * N⌋₊) ×ˢ (Finset.Icc 1 ⌊A * N⌋₊)).filter
      (fun p => F p.1 p.2 = N ∧ ((p.1 * p.2 : ℕ) : ℝ) ≤ A * N)) with hbox
  have hrt : ∀ N, rt A N = (box N).card := by
    intro N
    unfold rt
    rw [hbox]
  set Nset := (Finset.Icc 1 X).filter (fun N : ℕ => N % Q = ρ % Q) with hNset
  set Sg := E.sigma (fun e => (Finset.Icc 1 M).filter (· ∈ Coverage.Ge Q u e)) with hSg
  have hL : ∑ e ∈ E, (cnt (Coverage.Ge Q u e) ((X : ℝ) / (6 * σ)) : ℝ) = (Sg.card : ℝ) := by
    rw [hSg, Finset.card_sigma]
    push_cast
    rfl
  have hR : ∑ N ∈ Nset, (rt A N : ℝ) = ((∑ N ∈ Nset, (box N).card : ℕ) : ℝ) := by
    push_cast
    exact Finset.sum_congr rfl (fun N _ => by rw [hrt])
  rw [hL, hR]
  have h1 : Sg.card ≤ (Nset.biUnion box).card := by
    apply Finset.card_le_card_of_injOn (fun x : (Σ _ : ℕ, ℕ) => (x.1, h * x.2))
    · rintro ⟨e, t⟩ hx
      simp only [Finset.mem_coe, hSg, Finset.mem_sigma, Finset.mem_filter, Finset.mem_Icc] at hx
      obtain ⟨he, ⟨ht1, htM⟩, htSe, hHe6⟩ := hx
      have hc := hctx e he
      have hh1 : 1 ≤ h := hc.2.1
      have hep : e.Prime := hc.2.2.2.2.2.1
      obtain ⟨hF, -⟩ := hHe Q ρ h u e hc t htSe
      have hres := (hCR Q ρ h u e hc t htSe).2
      obtain ⟨hr1, hr2⟩ := hRR Q ρ h u e hc t htSe
      have hσ1 : (1 : ℝ) ≤ σ := by rw [hσdef]; exact_mod_cast le_trans hh1 (le_sig hh1)
      have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht1
      have hHeR : (t : ℝ) ≤ Coverage.He e t := by exact_mod_cast le_He e t
      have hHe6R : (Coverage.He e t : ℝ) ≤ 6 * t := by exact_mod_cast hHe6
      have hFR : (F e (h * t) : ℝ) = σ * Coverage.He e t := by rw [hF]; push_cast; rfl
      have hFpos : (0 : ℝ) < F e (h * t) := by rw [hFR]; nlinarith
      have htX : (t : ℝ) ≤ X / (6 * σ) := by
        have := Nat.floor_le (show (0 : ℝ) ≤ X / (6 * σ) by positivity)
        rw [← hM] at this
        exact le_trans (by exact_mod_cast htM) this
      have hFX : (F e (h * t) : ℝ) ≤ X := by
        rw [hFR]
        have h6 : 6 * σ * (t : ℝ) ≤ X := by
          rw [le_div_iff₀ (by positivity)] at htX
          linarith
        nlinarith
      have hehA := heA e he
      have hehtR : ((e * h * t : ℕ) : ℝ) ≤ A * F e (h * t) := by
        have h3 : ((e * h * t : ℕ) : ℝ) / F e (h * t) ≤ ((e * h : ℕ) : ℝ) := hr1.trans hr2
        rw [div_le_iff₀ hFpos] at h3
        have h4 : ((e * h : ℕ) : ℝ) ≤ A := by push_cast; exact hehA
        nlinarith
      have hN1 : 1 ≤ F e (h * t) := by
        have : (0 : ℝ) < F e (h * t) := hFpos
        exact_mod_cast this
      rw [Finset.mem_coe, Finset.mem_biUnion]
      refine ⟨F e (h * t), ?_, ?_⟩
      · rw [hNset, Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨hN1, by exact_mod_cast hFX⟩, hres⟩
      · rw [hbox]
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
        have hmul : ((e * (h * t) : ℕ) : ℝ) ≤ A * F e (h * t) := by
          rw [← mul_assoc]
          exact hehtR
        have he1 : 1 ≤ e := hep.one_lt.le
        have hht1 : 1 ≤ h * t := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
        have hle1 : e ≤ e * (h * t) := Nat.le_mul_of_pos_right e (by omega)
        have hle2 : h * t ≤ e * (h * t) := Nat.le_mul_of_pos_left (h * t) (by omega)
        refine ⟨⟨⟨he1, Nat.le_floor ?_⟩, ⟨hht1, Nat.le_floor ?_⟩⟩, trivial, hmul⟩
        · exact le_trans (by exact_mod_cast hle1) hmul
        · exact le_trans (by exact_mod_cast hle2) hmul
    · rintro ⟨e1, t1⟩ hx ⟨e2, t2⟩ hy heq
      rw [Finset.mem_coe, hSg, Finset.mem_sigma] at hx
      have hh1 : 1 ≤ h := (hctx e1 hx.1).2.1
      simp only [Prod.mk.injEq] at heq
      obtain ⟨he, ht⟩ := heq
      subst he
      have : t1 = t2 := Nat.eq_of_mul_eq_mul_left (by omega) ht
      subst this
      rfl
  have h2 : (Nset.biUnion box).card ≤ ∑ N ∈ Nset, (box N).card := Finset.card_biUnion_le
  exact_mod_cast h1.trans h2

theorem prod_one_sub_nonneg (Q e : ℕ) :
    0 ≤ ∏ p ∈ (Finset.range (e + 1)).filter (fun p : ℕ => p.Prime ∧ ¬ p ∣ Q),
      (1 - 1 / (p : ℝ)) := by
  apply Finset.prod_nonneg
  intro p hp
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Finset.mem_filter.1 hp).2.1.two_le
  rw [sub_nonneg, div_le_one (by linarith)]
  linarith

end Principia.Erdos1054.Proofs.ClassMoment

namespace Principia.Erdos1054.Proofs

open Principia.Erdos1054.Proofs.ClassMoment
open Finset Filter
open scoped Topology

theorem link_Eq_ClassLower : Spine.Link_Eq_ClassLower := by
  intro hU hGe hHe hCR hRR _hDP hMom hRefl Q hQ ρ h hh1 hg A hA
  obtain ⟨u, hu, huρ⟩ := hU Q hQ ρ h hg
  obtain ⟨C2, -, hmom, -⟩ := hMom 2 le_rfl
  set E := (Finset.range (⌊A / h⌋₊ + 1)).filter
    (fun e : ℕ => e.Prime ∧ max (max 2 h) Q < e ∧ e % Q = (Q - 1) % Q) with hE
  have hctx : ∀ e ∈ E, Coverage.ClassCtx Q ρ h u e := by
    intro e he
    rw [hE, Finset.mem_filter] at he
    exact ⟨hQ, hh1, hg, hu, huρ, he.2.1, he.2.2.1, he.2.2.2⟩
  have hhR : (0 : ℝ) < h := by exact_mod_cast (show 0 < h by omega)
  have heA : ∀ e ∈ E, (e : ℝ) * h ≤ A := by
    intro e he
    rw [hE, Finset.mem_filter, Finset.mem_range] at he
    have he' : e ≤ ⌊A / h⌋₊ := Nat.lt_succ_iff.1 he.1
    have h1 : (e : ℝ) ≤ A / h := (Nat.le_floor_iff (by positivity)).1 he'
    rwa [le_div_iff₀ hhR] at h1
  have hσ1 : (1 : ℝ) ≤ (sig h : ℝ) := by exact_mod_cast le_trans hh1 (le_sig hh1)
  have hQR : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  set v : ℕ → ℝ := fun X => (Q : ℝ) / X *
    ∑ N ∈ (Finset.Icc 1 X).filter (fun N : ℕ => N % Q = ρ % Q), (rt A N : ℝ) with hv
  have hbdd : IsBoundedUnder (· ≤ ·) atTop v := by
    apply isBoundedUnder_of_eventually_le (a := (Q : ℝ) * (1 + A ^ 3 * C2))
    filter_upwards [eventually_ge_atTop (⌈1 / A⌉₊ + 1)] with X hX
    have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
    have hXpos : (0 : ℝ) < X := by linarith
    have hAX : 1 ≤ A * X := by
      have h1 : 1 / A ≤ (X : ℝ) :=
        (Nat.le_ceil _).trans (by exact_mod_cast (show ⌈1 / A⌉₊ ≤ X by omega))
      rw [div_le_iff₀ hA] at h1
      linarith
    have h1 := sum_rt_le hRefl hA hmom X hAX
    have h2 : ∑ N ∈ (Finset.Icc 1 X).filter (fun N : ℕ => N % Q = ρ % Q), (rt A N : ℝ) ≤
        ∑ N ∈ Finset.Icc 1 X, (rt A N : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => by positivity)
    calc v X ≤ (Q : ℝ) / X * (X + A ^ 2 * (C2 * (A * X))) :=
          mul_le_mul_of_nonneg_left (h2.trans h1) (by positivity)
      _ = (Q : ℝ) * (1 + A ^ 3 * C2) := by
          field_simp
  have hcob : IsCoboundedUnder (· ≥ ·) atTop v := hbdd.isCoboundedUnder_ge
  have hδ : ∀ e, (Q : ℝ) * Coverage.deltaE Q e = ∏ p ∈ (Finset.range (e + 1)).filter
      (fun p : ℕ => p.Prime ∧ ¬ p ∣ Q), (1 - 1 / (p : ℝ)) := by
    intro e
    unfold Coverage.deltaE
    field_simp
  have key : ∀ ε > 0, 1 / (12 * (sig h : ℝ)) * ∑ e ∈ E, ∏ p ∈ (Finset.range (e + 1)).filter
      (fun p : ℕ => p.Prime ∧ ¬ p ∣ Q), (1 - 1 / (p : ℝ)) - ε ≤ liminf v atTop := by
    intro ε hε
    apply le_liminf_of_le hcob
    have hEc : (0 : ℝ) < E.card + 1 := by positivity
    set η : ℝ := ε * (6 * (sig h : ℝ)) / (Q * (E.card + 1)) with hη
    have hη0 : 0 < η := by
      rw [hη]
      apply div_pos (mul_pos hε (by linarith)) (mul_pos hQR hEc)
    have hev : ∀ e ∈ E, ∀ᶠ X : ℕ in atTop,
        (Coverage.deltaE Q e / 2 - η) * ((X : ℝ) / (6 * (sig h : ℝ))) ≤
          (cnt (Coverage.Ge Q u e) ((X : ℝ) / (6 * (sig h : ℝ))) : ℝ) := by
      intro e he
      have hlt : Coverage.deltaE Q e / 2 - η < lowerDens (Coverage.Ge Q u e) := by
        have := hGe Q ρ h u e (hctx e he)
        linarith
      obtain ⟨Y, hY⟩ := exists_mul_le_cnt_of_lt_lowerDens hlt
      filter_upwards [eventually_ge_atTop ⌈Y * (6 * (sig h : ℝ))⌉₊] with X hX
      apply hY
      rw [le_div_iff₀ (by linarith)]
      exact (Nat.le_ceil _).trans (by exact_mod_cast hX)
    filter_upwards [(Filter.eventually_all_finset E).2 hev, eventually_ge_atTop 1] with X hX hX1
    have hXpos : (0 : ℝ) < X := by exact_mod_cast hX1
    have hcount := lower_count hHe hCR hRR E hctx heA X
    set Sd := ∑ e ∈ E, Coverage.deltaE Q e with hSd
    have hprod : ∑ e ∈ E, ∏ p ∈ (Finset.range (e + 1)).filter
        (fun p : ℕ => p.Prime ∧ ¬ p ∣ Q), (1 - 1 / (p : ℝ)) = (Q : ℝ) * Sd := by
      rw [hSd, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun e _ => (hδ e).symm)
    have hk : (Q : ℝ) / (6 * (sig h : ℝ)) * ((E.card : ℝ) * η) =
        ε * (E.card / (E.card + 1)) := by
      rw [hη]
      field_simp
    have hk2 : ε * ((E.card : ℝ) / (E.card + 1)) ≤ ε :=
      mul_le_of_le_one_right hε.le (div_le_one_of_le₀ (by linarith) hEc.le)
    have stepA : 1 / (12 * (sig h : ℝ)) * ∑ e ∈ E, ∏ p ∈ (Finset.range (e + 1)).filter
        (fun p : ℕ => p.Prime ∧ ¬ p ∣ Q), (1 - 1 / (p : ℝ)) - ε ≤
        (Q : ℝ) / (6 * (sig h : ℝ)) * ∑ e ∈ E, (Coverage.deltaE Q e / 2 - η) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.sum_div, ← hSd, hprod,
        mul_sub, hk]
      have : 1 / (12 * (sig h : ℝ)) * ((Q : ℝ) * Sd) =
          (Q : ℝ) / (6 * (sig h : ℝ)) * (Sd / 2) := by
        field_simp
        ring
      rw [this]
      linarith
    calc _ ≤ (Q : ℝ) / (6 * (sig h : ℝ)) * ∑ e ∈ E, (Coverage.deltaE Q e / 2 - η) := stepA
      _ = (Q : ℝ) / X * ((∑ e ∈ E, (Coverage.deltaE Q e / 2 - η)) *
            ((X : ℝ) / (6 * (sig h : ℝ)))) := by
          field_simp
      _ = (Q : ℝ) / X * ∑ e ∈ E, (Coverage.deltaE Q e / 2 - η) *
            ((X : ℝ) / (6 * (sig h : ℝ))) := by
          rw [Finset.sum_mul]
      _ ≤ (Q : ℝ) / X * ∑ e ∈ E,
            (cnt (Coverage.Ge Q u e) ((X : ℝ) / (6 * (sig h : ℝ))) : ℝ) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum hX) (by positivity)
      _ ≤ (Q : ℝ) / X *
            ∑ N ∈ (Finset.Icc 1 X).filter (fun N : ℕ => N % Q = ρ % Q), (rt A N : ℝ) :=
          mul_le_mul_of_nonneg_left hcount (by positivity)
  have hmain := le_of_forall_sub_le key
  unfold Coverage.lamLower
  exact hmain

theorem link_Prop_ClassFirstMoment_bound : Spine.Link_Prop_ClassFirstMoment_bound := by
  intro hH hCL hMQ hCPS Q hQ ρ
  obtain ⟨h, hh1, hg⟩ := hH Q hQ ρ
  have hφ : (0 : ℝ) < Q.totient := by exact_mod_cast Nat.totient_pos.2 (by omega)
  have hQR : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh1
  have hσ : (1 : ℝ) ≤ (sig h : ℝ) := by exact_mod_cast le_trans hh1 (le_sig hh1)
  set K : ℝ := (Q : ℝ) / Q.totient * Real.exp (-eulerGamma) with hK
  have hK0 : 0 < K := by
    rw [hK]
    exact mul_pos (div_pos hQR hφ) (Real.exp_pos _)
  obtain ⟨y0, hy0⟩ := eventually_atTop.1 ((hMQ Q hQ).eventually (lt_mem_nhds (half_lt_self hK0)))
  obtain ⟨Z0, hZ0⟩ := eventually_atTop.1
    ((hCPS Q hQ).eventually (lt_mem_nhds (show (1 : ℝ) / 2 < 1 by norm_num)))
  set N1 : ℕ := max (max (max 2 h) Q) ⌈y0⌉₊ with hN1
  have hN12 : 2 ≤ N1 := le_trans (le_trans (le_max_left 2 h) (le_max_left _ Q)) (le_max_left _ _)
  set C0 : ℝ := ∑ e ∈ (Finset.Iic N1).filter (fun e : ℕ => e.Prime ∧ e % Q = (Q - 1) % Q),
    1 / Real.log e with hC0
  have hlog_nn : ∀ e : ℕ, 0 ≤ 1 / Real.log e := fun e => by
    have := Real.log_natCast_nonneg e
    positivity
  have hC0nn : 0 ≤ C0 := Finset.sum_nonneg (fun e _ => hlog_nn e)
  have hP : ∀ e : ℕ, N1 < e → K / 2 / Real.log e ≤ ∏ p ∈ (Finset.range (e + 1)).filter
      (fun p : ℕ => p.Prime ∧ ¬ p ∣ Q), (1 - 1 / (p : ℝ)) := by
    intro e he
    have hey0 : y0 ≤ (e : ℝ) :=
      (Nat.le_ceil y0).trans (by exact_mod_cast (le_max_right _ _).trans he.le)
    have h1 := hy0 e hey0
    rw [Nat.floor_natCast, ← Nat.range_succ_eq_Iic] at h1
    have he2 : (1 : ℝ) < e := by exact_mod_cast (show 1 < e by omega)
    rw [div_le_iff₀ (Real.log_pos he2)]
    exact h1.le
  set c : ℝ := K / (96 * (sig h : ℝ) * h * Q.totient) with hc
  have hcpos : 0 < c := by
    rw [hc]
    exact div_pos hK0 (mul_pos (mul_pos (mul_pos (by norm_num) (by linarith)) (by linarith)) hφ)
  refine ⟨c, hcpos, ?_⟩
  have hdiv : Tendsto (fun A : ℝ => A / h) atTop atTop := tendsto_id.atTop_div_const (by linarith)
  obtain ⟨A₀, hA₀⟩ := eventually_atTop.1
    (((hdiv.eventually_gt_atTop 1).and (hdiv.eventually_ge_atTop Z0)).and
      ((tendsto_div_log_pow_atTop 2).eventually_ge_atTop (4 * C0 * Q.totient * h)))
  refine ⟨A₀, fun A hA => ?_⟩
  obtain ⟨⟨h1A, hZA⟩, hbig⟩ := hA₀ A hA
  have hAh : (h : ℝ) < A := by
    have h1A' : (1 : ℝ) < A / h := h1A
    rw [lt_div_iff₀ (by linarith)] at h1A'
    linarith
  have hA1 : 1 < A := by linarith
  have hApos : 0 < A := by linarith
  have hCL' := hCL Q hQ ρ h hh1 hg A hApos
  set E := (Finset.range (⌊A / h⌋₊ + 1)).filter
    (fun e : ℕ => e.Prime ∧ max (max 2 h) Q < e ∧ e % Q = (Q - 1) % Q) with hE
  set B := (Finset.Iic ⌊A / h⌋₊).filter (fun e : ℕ => e.Prime ∧ e % Q = (Q - 1) % Q) with hB
  set T1 := ∑ e ∈ E.filter (fun e => N1 < e), 1 / Real.log e with hT1
  have hsplit : ∑ e ∈ B, 1 / Real.log e ≤ T1 + C0 := by
    rw [← Finset.sum_filter_add_sum_filter_not B (fun e => N1 < e)]
    apply add_le_add
    · apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro e he
        rw [hB, Finset.mem_filter, Finset.mem_filter, Finset.mem_Iic] at he
        rw [Finset.mem_filter, hE, Finset.mem_filter, Finset.mem_range]
        have hmx : max (max 2 h) Q ≤ N1 := le_max_left _ _
        exact ⟨⟨by omega, he.1.2.1, by omega, he.1.2.2⟩, he.2⟩
      · intro e _ _
        exact hlog_nn e
    · apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro e he
        rw [hB, Finset.mem_filter, Finset.mem_filter] at he
        rw [Finset.mem_filter, Finset.mem_Iic]
        exact ⟨by omega, he.1.2⟩
      · intro e _ _
        exact hlog_nn e
  have hSZ : (1 : ℝ) / 2 < (∑ e ∈ B, 1 / Real.log e) /
      (A / h / (Q.totient * Real.log (A / h) ^ 2)) := hZ0 (A / h) hZA
  have hLh : 0 < Real.log (A / h) := Real.log_pos h1A
  have hL : 0 < Real.log A := Real.log_pos hA1
  have hLle : Real.log (A / h) ≤ Real.log A :=
    Real.log_le_log (by positivity) (div_le_self hApos.le hhR)
  have hD : 0 < A / h / (Q.totient * Real.log (A / h) ^ 2) := by positivity
  set W : ℝ := A / h / (Q.totient * Real.log A ^ 2) with hW
  have hWD : W ≤ A / h / (Q.totient * Real.log (A / h) ^ 2) := by
    rw [hW]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    have : Real.log (A / h) ^ 2 ≤ Real.log A ^ 2 := pow_le_pow_left₀ hLh.le hLle 2
    exact mul_le_mul_of_nonneg_left this hφ.le
  have hSW : W / 2 < ∑ e ∈ B, 1 / Real.log e := by
    rw [lt_div_iff₀ hD] at hSZ
    linarith
  have hC0W : C0 ≤ W / 4 := by
    have hbig' : 4 * C0 * Q.totient * h ≤ A / Real.log A ^ 2 := hbig
    have hW' : W / 4 = A / Real.log A ^ 2 / (4 * Q.totient * h) := by
      rw [hW]
      field_simp
    rw [hW', le_div_iff₀ (by positivity)]
    linarith
  have hT1W : W / 4 ≤ T1 := by linarith
  have hsumP : K / 2 * T1 ≤ ∑ e ∈ E, ∏ p ∈ (Finset.range (e + 1)).filter
      (fun p : ℕ => p.Prime ∧ ¬ p ∣ Q), (1 - 1 / (p : ℝ)) := by
    rw [hT1, Finset.mul_sum]
    calc ∑ e ∈ E.filter (fun e => N1 < e), K / 2 * (1 / Real.log e)
        ≤ ∑ e ∈ E.filter (fun e => N1 < e), ∏ p ∈ (Finset.range (e + 1)).filter
            (fun p : ℕ => p.Prime ∧ ¬ p ∣ Q), (1 - 1 / (p : ℝ)) := by
          apply Finset.sum_le_sum
          intro e he
          rw [mul_one_div]
          exact hP e (Finset.mem_filter.1 he).2
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun e _ _ => prod_one_sub_nonneg Q e)
  have hfinal : c * (A / Real.log A ^ 2) = 1 / (12 * (sig h : ℝ)) * (K / 2 * (W / 4)) := by
    rw [hc, hW]
    field_simp
    ring
  rw [hfinal]
  refine le_trans ?_ hCL'
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  refine le_trans ?_ hsumP
  exact mul_le_mul_of_nonneg_left hT1W (by linarith)

end Principia.Erdos1054.Proofs
