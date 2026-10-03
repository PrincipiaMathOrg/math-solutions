/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Erdos1054.Spine
import Principia.Erdos1054.Density
import Principia.Erdos1054.Basic
import Mathlib.Combinatorics.Enumerative.InclusionExclusion
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option autoImplicit false

/-!
# Erdős 1054 (EP1054.tex) — periodic obstructions for bounded cofactors (§5.2)

Proofs of the package `Envelope` of `Campaigns/Erdos-1054/LEAN-WORKLIST.md`: paper lines 1979–2062
(the moduli `𝒦_A`, the periodic set `V_A` of integers divisible by none of them, its density,
`prop:fm-envelope`, and `cor:fm-envelope-tail`).

* `link_UpperTails_Claim_KA_finite` — `𝒦_A` equals its finite presentation `KAfin A`: the witness
  `d₀ = M/g ≤ M ∣ Λ(A)` has the same `D`, hence the same `K` (uses `Lem_FmModulus`'s divisibility
  clause; the `Fact_KmodGeTwo` hypothesis is not consumed, `M > 0` being re-derived);
* `link_UpperTails_Claim_VA_periodic` — every `k ∈ 𝒦_A` divides `W_A`;
* `link_UpperTails_Claim_VA_density` — inclusion–exclusion (Mathlib
  `Finset.indicator_biUnion_eq_sum_powerset`) turns the count of `V_A` into a finite signed sum of
  counts of multiples of `lcm(I)`, so `V_A` has density `dV A`; the integers coprime to `W_A` lie in
  `V_A` (`K ≥ 2`). The `Claim_VA_periodic` hypothesis is not consumed (the density comes from the
  finite linear combination, not from a period);
* `leaf_UpperTails_Claim_VA_rough` — `K_{p,1} = p`;
* `link_Prop_FmEnvelope` — `G_A ∩ V_A ⊆ σ(ℕ) ∪ {F_e(d) : 2 ≤ e ≤ A, W_A ∤ σ(ed)}`, the second set
  counted by `⌊A⌋ · #{n ≤ ⌊A⌋X : W_A ∤ σ(n)}`;
* `link_UpperTails_Claim_DeltaPfix` — `log P / B → 2` (`B = log A log₂A / log₃A`) by squeezing
  `log⌊A^θ⌋` between `θ log A − log 2` and `θ log A`, then Mertens 3 along `P → ∞`;
* `link_UpperTails_Claim_RoughNotVA` — every `P`-rough `k ∈ 𝒦_A` is `C(e, M) ≥ M` with `e ∣ M`,
  `M ∣ Λ(A)`, `M > P/A`, so `∑ 1/k ≤ S(A, P/A)`; the `P`-rough multiples of `k` have upper density
  `≤ Δ(P)/k`. Threshold `A ≥ e^{e²}` (which gives `A < P`). `Lem_FmModulus` is not consumed
  (`M ∣ ed` is elementary);
* `link_Cor_FmEnvelopeTail` — upper bound from `V_A ⊆ {A-rough}` (for every `A ≥ 2`); lower bound
  `d(V_A) ≥ Δ(P)(1 − S(A, P/A))`, with `S → 0` by `eq:fixed-kernel-tail`.
-/

namespace Principia.Erdos1054.Proofs.Envelope

open Finset Filter Principia.Erdos1054 Principia.Erdos1054.UpperTails
open scoped Topology

lemma mem_Dset {e d j : ℕ} : j ∈ Dset e d ↔ 1 ≤ j ∧ j < e ∧ j ∣ e * d := by
  unfold Dset
  rw [Finset.mem_filter, Finset.mem_Ico, and_assoc]

lemma Mlcm_pos (e d : ℕ) : 0 < Mlcm e d := by
  unfold Mlcm
  refine Nat.pos_of_ne_zero fun h => ?_
  rw [Finset.lcm_eq_zero_iff] at h
  obtain ⟨x, hx, hx0⟩ := h
  have h1 := (mem_Dset.1 hx).1
  simp only [id] at hx0
  omega

lemma dvd_Mlcm {e d j : ℕ} (h : j ∈ Dset e d) : j ∣ Mlcm e d :=
  Finset.dvd_lcm (f := id) h

lemma Mlcm_dvd {e d : ℕ} : Mlcm e d ∣ e * d :=
  Finset.lcm_dvd fun _ hj => (mem_Dset.1 hj).2.2

lemma Mlcm_congr {e d d' : ℕ} (h : Dset e d = Dset e d') : Mlcm e d = Mlcm e d' := by
  unfold Mlcm
  rw [h]

lemma Csum_congr {e d d' : ℕ} (h : Dset e d = Dset e d') : Csum e d = Csum e d' := by
  unfold Csum
  rw [Mlcm_congr h, h]

lemma Kmod_congr {e d d' : ℕ} (h : Dset e d = Dset e d') : Kmod e d = Kmod e d' := by
  unfold Kmod
  rw [Mlcm_congr h, Csum_congr h]

lemma lcmUpTo_pos (A : ℝ) : 0 < lcmUpTo A := by
  unfold lcmUpTo
  refine Nat.pos_of_ne_zero fun h => ?_
  rw [Finset.lcm_eq_zero_iff] at h
  obtain ⟨x, hx, hx0⟩ := h
  rw [Finset.mem_Icc] at hx
  simp only [id] at hx0
  omega

/-- `M = lcm(D) ∣ Λ(A)` whenever `e ≤ ⌊A⌋`. -/
lemma Mlcm_dvd_lcmUpTo {e d : ℕ} {A : ℝ} (hea : e ≤ ⌊A⌋₊) : Mlcm e d ∣ lcmUpTo A := by
  unfold lcmUpTo Mlcm
  apply Finset.lcm_mono
  intro j hj
  rw [mem_Dset] at hj
  rw [Finset.mem_Icc]
  omega

lemma mem_KAfin {A : ℝ} {k : ℕ} :
    k ∈ KAfin A ↔ ∃ e d, (2 ≤ e ∧ e ≤ ⌊A⌋₊) ∧ (1 ≤ d ∧ d ≤ lcmUpTo A) ∧ Kmod e d = k := by
  unfold KAfin
  rw [Finset.mem_image]
  constructor
  · rintro ⟨⟨e, d⟩, hq, rfl⟩
    rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hq
    exact ⟨e, d, hq.1, hq.2, rfl⟩
  · rintro ⟨e, d, he, hd, rfl⟩
    exact ⟨(e, d), Finset.mem_product.2 ⟨Finset.mem_Icc.2 he, Finset.mem_Icc.2 hd⟩, rfl⟩

/-! ## `Claim_KA_finite` -/

theorem kA_finite (hFM : Lem_FmModulus) : UpperTails.Claim_KA_finite := by
  intro A hA
  have hA0 : (0 : ℝ) ≤ A := by linarith
  ext k
  rw [Finset.mem_coe, mem_KAfin]
  simp only [KA, Set.mem_setOf_eq]
  constructor
  · rintro ⟨e, d, ⟨he2, hea⟩, ⟨hd1, _⟩, rfl⟩
    exact ⟨e, d, he2, (Nat.le_floor_iff hA0).1 hea, hd1, rfl⟩
  · rintro ⟨e, d, he2, heA, hd1, rfl⟩
    have hea : e ≤ ⌊A⌋₊ := Nat.le_floor heA
    have hM := Mlcm_pos e d
    have hg0 : 0 < Nat.gcd e (Mlcm e d) := Nat.gcd_pos_of_pos_left _ (by omega)
    have hgM : Nat.gcd e (Mlcm e d) ∣ Mlcm e d := Nat.gcd_dvd_right _ _
    have hge : Nat.gcd e (Mlcm e d) ∣ e := Nat.gcd_dvd_left _ _
    have hd0 : 1 ≤ Mlcm e d / Nat.gcd e (Mlcm e d) := Nat.div_pos (Nat.le_of_dvd hM hgM) hg0
    have hed0 : e * (Mlcm e d / Nat.gcd e (Mlcm e d)) =
        e / Nat.gcd e (Mlcm e d) * Mlcm e d := by
      rw [← Nat.mul_div_assoc e hgM, Nat.mul_div_right_comm hge]
    have hdiv : Mlcm e d / Nat.gcd e (Mlcm e d) ∣ d := (hFM e d he2 hd1).2.1
    have hD : Dset e (Mlcm e d / Nat.gcd e (Mlcm e d)) = Dset e d := by
      ext j
      rw [mem_Dset, mem_Dset]
      constructor
      · rintro ⟨h1, h2, h3⟩
        exact ⟨h1, h2, h3.trans (Nat.mul_dvd_mul_left e hdiv)⟩
      · rintro ⟨h1, h2, h3⟩
        refine ⟨h1, h2, ?_⟩
        rw [hed0]
        exact (dvd_Mlcm (mem_Dset.2 ⟨h1, h2, h3⟩)).trans (dvd_mul_left _ _)
    refine ⟨e, Mlcm e d / Nat.gcd e (Mlcm e d), ⟨he2, hea⟩, ⟨hd0, ?_⟩, Kmod_congr hD⟩
    exact (Nat.div_le_self _ _).trans (Nat.le_of_dvd (lcmUpTo_pos A) (Mlcm_dvd_lcmUpTo hea))

/-- Under `Claim_KA_finite`, membership in `𝒦_A` is membership in the finset `KAfin A`. -/
lemma mem_KA_iff (hK : UpperTails.Claim_KA_finite) {A : ℝ} (hA : 2 ≤ A) {k : ℕ} :
    k ∈ KA A ↔ k ∈ KAfin A := by
  rw [← hK A hA, Finset.mem_coe]

lemma dvd_WA {A : ℝ} {k : ℕ} (hk : k ∈ KAfin A) : k ∣ WA A :=
  Finset.dvd_lcm (f := id) hk

/-! ## `Claim_VA_periodic` -/

theorem vA_periodic (hK : UpperTails.Claim_KA_finite) : UpperTails.Claim_VA_periodic := by
  intro A hA N M hNM
  have key : ∀ k ∈ KA A, (k ∣ N ↔ k ∣ M) := fun k hk =>
    hNM.dvd_iff (dvd_WA ((mem_KA_iff hK hA).1 hk))
  simp only [VA, Set.mem_setOf_eq]
  constructor
  · intro h k hk hkM
    exact h k hk ((key k hk).2 hkM)
  · intro h k hk hkN
    exact h k hk ((key k hk).1 hkN)

/-! ## `Claim_VA_rough` -/

lemma Kmod_prime_one {p : ℕ} (hp : p.Prime) : Kmod p 1 = p := by
  have hD : Dset p 1 = {1} := by
    ext j
    rw [mem_Dset, Finset.mem_singleton]
    constructor
    · rintro ⟨h1, h2, h3⟩
      rw [mul_one] at h3
      rcases (Nat.dvd_prime hp).1 h3 with h | h
      · exact h
      · omega
    · rintro rfl
      exact ⟨le_rfl, hp.one_lt, one_dvd _⟩
  have hM : Mlcm p 1 = 1 := by
    unfold Mlcm
    rw [hD]
    simp
  have hC : Csum p 1 = 1 := by
    unfold Csum
    rw [hM, hD]
    simp
  unfold Kmod
  rw [hM, hC]
  simp

theorem vA_rough : UpperTails.Claim_VA_rough := by
  intro A _
  have hprime : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ A → p ∈ KA A := fun p hp hpA =>
    ⟨p, 1, hp.two_le, hpA, le_rfl, (Kmod_prime_one hp).symm⟩
  refine ⟨hprime, fun N hN p hp => ?_⟩
  by_contra hlt
  exact hN p (hprime p (Nat.prime_of_mem_primeFactors hp) (not_lt.1 hlt))
    (Nat.dvd_of_mem_primeFactors hp)

/-! ## Inclusion–exclusion for the density of `{N : k ∤ N ∀ k ∈ K}` -/

lemma cnt_eq_sum_indicator (S : Set ℕ) (n : ℕ) :
    (cnt S (n : ℝ) : ℝ) = ∑ N ∈ Finset.Icc 1 n, S.indicator (fun _ => (1 : ℝ)) N := by
  classical
  rw [cnt_natCast, Finset.sum_indicator_eq_sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]

lemma lcm_pos_of_subset {K I : Finset ℕ} (hK : ∀ k ∈ K, 1 ≤ k) (hI : I ⊆ K) : 0 < I.lcm id := by
  refine Nat.pos_of_ne_zero fun h => ?_
  rw [Finset.lcm_eq_zero_iff] at h
  obtain ⟨x, hx, hx0⟩ := h
  have := hK x (hI hx)
  simp only [id] at hx0
  omega

theorem hasDens_not_dvd_any (K : Finset ℕ) (hK : ∀ k ∈ K, 1 ≤ k) :
    HasDens {N | ∀ k ∈ K, ¬ k ∣ N}
      (1 - ∑ I ∈ K.powerset.filter (fun I => I.Nonempty),
        (-1 : ℝ) ^ (I.card + 1) / ((I.lcm id : ℕ) : ℝ)) := by
  classical
  set U : Set ℕ := ⋃ k ∈ K, {N : ℕ | k ∣ N} with hU
  have hinter : ∀ t : Finset ℕ, (⋂ k ∈ t, {N : ℕ | k ∣ N}) = {N : ℕ | t.lcm id ∣ N} := by
    intro t
    ext N
    simp only [Set.mem_iInter, Set.mem_setOf_eq, Finset.lcm_dvd_iff, id]
  have hpt : ∀ N : ℕ, U.indicator (fun _ => (1 : ℝ)) N =
      ∑ t ∈ K.powerset.filter (fun I => I.Nonempty),
        (-1 : ℤ) ^ (t.card + 1) • ({N : ℕ | t.lcm id ∣ N} : Set ℕ).indicator (fun _ => (1 : ℝ)) N := by
    intro N
    rw [hU, Finset.indicator_biUnion_eq_sum_powerset]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [hinter t]
  have hcnt : ∀ n : ℕ, (cnt U (n : ℝ) : ℝ) / n =
      ∑ t ∈ K.powerset.filter (fun I => I.Nonempty),
        (-1 : ℤ) ^ (t.card + 1) • ((cnt {N : ℕ | t.lcm id ∣ N} (n : ℝ) : ℝ) / n) := by
    intro n
    rw [cnt_eq_sum_indicator]
    simp_rw [hpt]
    rw [Finset.sum_comm, Finset.sum_div]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← Finset.smul_sum, cnt_eq_sum_indicator, smul_div_assoc]
  have hU' : HasDens U (∑ t ∈ K.powerset.filter (fun I => I.Nonempty),
      (-1 : ℤ) ^ (t.card + 1) • (1 / ((t.lcm id : ℕ) : ℝ))) := by
    unfold HasDens
    simp_rw [hcnt]
    refine tendsto_finsetSum _ fun t ht => ?_
    have hpos : 1 ≤ t.lcm id :=
      lcm_pos_of_subset hK (Finset.mem_powerset.1 (Finset.mem_filter.1 ht).1)
    exact (hasDens_dvd hpos).const_smul _
  have hcompl : {N | ∀ k ∈ K, ¬ k ∣ N} = Uᶜ := by
    ext N
    simp only [hU, Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_iUnion, not_exists]
  rw [hcompl]
  convert hU'.compl using 2
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [zsmul_eq_mul]
  push_cast
  ring

/-! ## `Claim_VA_density` -/

lemma two_le_of_mem_KAfin (hKG : Fact_KmodGeTwo) {A : ℝ} {k : ℕ} (hk : k ∈ KAfin A) : 2 ≤ k := by
  obtain ⟨e, d, ⟨he, _⟩, ⟨hd, _⟩, rfl⟩ := mem_KAfin.1 hk
  exact (hKG e d he hd).2.2.2.1

lemma VA_eq (hK : UpperTails.Claim_KA_finite) {A : ℝ} (hA : 2 ≤ A) :
    VA A = {N | ∀ k ∈ KAfin A, ¬ k ∣ N} := by
  ext N
  simp only [VA, Set.mem_setOf_eq, mem_KA_iff hK hA]

lemma hasDens_coprime {W : ℕ} (hW : 0 < W) :
    HasDens {N | Nat.Coprime N W} ((W.totient : ℝ) / W) := by
  have h := hasDens_of_periodic hW (S := {N | Nat.Coprime N W})
    (fun N => by simp only [Set.mem_setOf_eq, Nat.coprime_add_self_left])
  have hc : cnt {N | Nat.Coprime N W} (W : ℝ) = W.totient := by
    classical
    rw [cnt_natCast, ← Nat.filter_coprime_Ico_eq_totient W 1]
    congr 1
    ext x
    rw [mem_cntFinset, Finset.mem_filter, Finset.mem_Ico, Set.mem_setOf_eq, Nat.coprime_comm]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨h1, by omega⟩, h3⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨h1, by omega⟩, h3⟩
  rwa [hc] at h

theorem vA_density (hK : UpperTails.Claim_KA_finite) (hKG : Fact_KmodGeTwo) :
    UpperTails.Claim_VA_density := by
  intro A hA
  have hD : HasDens (VA A) (dV A) := by
    rw [VA_eq hK hA]
    unfold dV
    exact hasDens_not_dvd_any _ (fun k hk => by have := two_le_of_mem_KAfin hKG hk; omega)
  have hW : 0 < WA A := by
    unfold WA
    exact lcm_pos_of_subset (K := KAfin A)
      (fun k hk => by have := two_le_of_mem_KAfin hKG hk; omega) subset_rfl
  have hsub : {N | Nat.Coprime N (WA A)} ⊆ VA A := by
    intro N hN
    rw [VA_eq hK hA]
    intro k hk hkN
    have h1 : k ∣ Nat.gcd N (WA A) := Nat.dvd_gcd hkN (dvd_WA hk)
    rw [Set.mem_setOf_eq] at hN
    rw [hN] at h1
    have := two_le_of_mem_KAfin hKG hk
    have := Nat.le_of_dvd one_pos h1
    omega
  have hcop := hasDens_coprime hW
  refine ⟨hD, ?_, ?_⟩
  · rw [← hcop.lowerDens_eq, ← hD.lowerDens_eq]
    exact lowerDens_mono hsub
  · have h1 : (0 : ℝ) < (WA A).totient := by exact_mod_cast Nat.totient_pos.2 hW
    have h2 : (0 : ℝ) < WA A := by exact_mod_cast hW
    exact div_pos h1 h2

/-! ## `prop:fm-envelope` -/

/-- `F_1(d) = σ(d)`: every divisor of `d` is at most `d`. -/
lemma F_one (d : ℕ) : F 1 d = sig d := by
  unfold F
  rw [one_mul, sig, ArithmeticFunction.sigma_one_apply]
  exact Finset.sum_congr (Finset.filter_true_of_mem fun q hq => Nat.divisor_le hq) fun _ _ => rfl

open Classical in
/-- Counting through a two-parameter image: if every `N ∈ S ∩ [1, X]` is `φ e n` with
`2 ≤ e ≤ a` and `n ∈ B ∩ [1, Y]`, then `cnt S X ≤ a · cnt B Y`. -/
lemma cnt_le_mul_cnt_of_image {S B : Set ℕ} (a : ℕ) (φ : ℕ → ℕ → ℕ) {X Y : ℝ}
    (h : ∀ N, 1 ≤ N → N ≤ ⌊X⌋₊ → N ∈ S →
      ∃ e n, 2 ≤ e ∧ e ≤ a ∧ 1 ≤ n ∧ n ≤ ⌊Y⌋₊ ∧ n ∈ B ∧ φ e n = N) :
    cnt S X ≤ a * cnt B Y := by
  unfold cnt
  calc ((Finset.Icc 1 ⌊X⌋₊).filter (· ∈ S)).card
      ≤ ((Finset.Icc 2 a ×ˢ (Finset.Icc 1 ⌊Y⌋₊).filter (· ∈ B)).image
          (fun q => φ q.1 q.2)).card := by
        apply Finset.card_le_card
        intro N hN
        rw [mem_cntFinset] at hN
        obtain ⟨e, n, h1, h2, h3, h4, h5, h6⟩ := h N hN.1.1 hN.1.2 hN.2
        rw [Finset.mem_image]
        exact ⟨(e, n), Finset.mem_product.2 ⟨Finset.mem_Icc.2 ⟨h1, h2⟩,
          mem_cntFinset.2 ⟨⟨h3, h4⟩, h5⟩⟩, h6⟩
    _ ≤ (Finset.Icc 2 a ×ˢ (Finset.Icc 1 ⌊Y⌋₊).filter (· ∈ B)).card := Finset.card_image_le
    _ ≤ a * ((Finset.Icc 1 ⌊Y⌋₊).filter (· ∈ B)).card := by
        rw [Finset.card_product, Nat.card_Icc]
        exact Nat.mul_le_mul_right _ (by omega)

/-- The targets `F_e(d)` (`2 ≤ e ≤ a`) whose source `n = e d` has `W ∤ σ(n)` have density zero
when the sources do. -/
lemma densZero_badTargets {a W : ℕ} (ha : 1 ≤ a) (hB : DensZero {n : ℕ | ¬ W ∣ sig n}) :
    DensZero {N : ℕ | ∃ e d, 2 ≤ e ∧ e ≤ a ∧ 1 ≤ d ∧ N = F e d ∧ ¬ W ∣ sig (e * d)} := by
  rw [densZero_iff_exists_real]
  intro ε hε
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have ha0 : (0 : ℝ) < a := by linarith
  obtain ⟨Y₀, hY₀⟩ := hB.exists_le_mul (ε := ε / ((a : ℝ) * a)) (by positivity)
  refine ⟨max Y₀ 0, fun X hX => ?_⟩
  have hX0 : 0 ≤ X := le_trans (le_max_right _ _) hX
  have hcnt := cnt_le_mul_cnt_of_image (S := {N : ℕ | ∃ e d, 2 ≤ e ∧ e ≤ a ∧ 1 ≤ d ∧
      N = F e d ∧ ¬ W ∣ sig (e * d)}) (B := {n : ℕ | ¬ W ∣ sig n}) a
      (fun e n => F e (n / e)) (X := X) (Y := (a : ℝ) * X) (by
    intro N _ hNX hN
    obtain ⟨e, d, he2, hea, hd1, rfl, hW⟩ := hN
    refine ⟨e, e * d, he2, hea, Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)),
      ?_, hW, ?_⟩
    · apply Nat.le_floor
      have hdF := F_ge e d (by omega) hd1
      have hle : e * d ≤ a * ⌊X⌋₊ := Nat.mul_le_mul hea (hdF.trans hNX)
      calc ((e * d : ℕ) : ℝ) ≤ ((a * ⌊X⌋₊ : ℕ) : ℝ) := by exact_mod_cast hle
        _ = (a : ℝ) * (⌊X⌋₊ : ℝ) := by push_cast; ring
        _ ≤ (a : ℝ) * X := mul_le_mul_of_nonneg_left (Nat.floor_le hX0) ha0.le
    · show F e (e * d / e) = F e d
      rw [Nat.mul_div_cancel_left d (by omega)])
  have hY : Y₀ ≤ (a : ℝ) * X := by
    have : X ≤ (a : ℝ) * X := by nlinarith
    exact le_trans (le_trans (le_max_left _ _) hX) this
  have h2 := hY₀ _ hY
  have hcntR : (cnt {N : ℕ | ∃ e d, 2 ≤ e ∧ e ≤ a ∧ 1 ≤ d ∧ N = F e d ∧ ¬ W ∣ sig (e * d)} X : ℝ)
      ≤ a * (cnt {n : ℕ | ¬ W ∣ sig n} ((a : ℝ) * X) : ℝ) := by exact_mod_cast hcnt
  calc _ ≤ a * (cnt {n : ℕ | ¬ W ∣ sig n} ((a : ℝ) * X) : ℝ) := hcntR
    _ ≤ a * (ε / ((a : ℝ) * a) * ((a : ℝ) * X)) := mul_le_mul_of_nonneg_left h2 ha0.le
    _ = ε * X := by field_simp

theorem prop_fmEnvelope (hSR : Lem_SigmaRangeZero) (hFM : Lem_FmModulus)
    (hFMN : Lem_FixedModulusNormality) (hK : UpperTails.Claim_KA_finite)
    (hVD : UpperTails.Claim_VA_density) : Prop_FmEnvelope := by
  intro A hA
  have hA0 : (0 : ℝ) ≤ A := by linarith
  have ha2 : 2 ≤ ⌊A⌋₊ := Nat.le_floor (by exact_mod_cast hA)
  obtain ⟨hV, _, hpos⟩ := hVD A hA
  have hW1 : 1 ≤ WA A := by
    rcases Nat.eq_zero_or_pos (WA A) with h | h
    · rw [h] at hpos
      simp at hpos
    · exact h
  have hB : DensZero {n : ℕ | ¬ WA A ∣ sig n} := hFMN (WA A) hW1
  have hT := densZero_badTargets (a := ⌊A⌋₊) (by omega) hB
  have hsub : Gcov ⌊A⌋₊ ∩ VA A ⊆ {N : ℕ | ∃ n : ℕ, 1 ≤ n ∧ sig n = N} ∪
      {N : ℕ | ∃ e d, 2 ≤ e ∧ e ≤ ⌊A⌋₊ ∧ 1 ≤ d ∧ N = F e d ∧ ¬ WA A ∣ sig (e * d)} := by
    rintro N ⟨⟨e, d, he1, hea, hd1, rfl⟩, hNV⟩
    rcases Nat.lt_or_ge e 2 with he | he
    · left
      have : e = 1 := by omega
      subst this
      exact ⟨d, hd1, (F_one d).symm⟩
    · right
      refine ⟨e, d, he, hea, hd1, rfl, fun hWd => ?_⟩
      have hkK : Kmod e d ∈ KA A := ⟨e, d, he, (Nat.le_floor_iff hA0).1 hea, hd1, rfl⟩
      have hkW : Kmod e d ∣ WA A := dvd_WA ((mem_KA_iff hK hA).1 hkK)
      have hcong : F e d ≡ sig (e * d) [MOD Kmod e d] := (hFM e d he hd1).2.2.1
      exact hNV (Kmod e d) hkK ((hcong.dvd_iff dvd_rfl).2 (hkW.trans hWd))
  have hGV : DensZero (Gcov ⌊A⌋₊ ∩ VA A) := densZero_subset (densZero_union hSR hT) hsub
  refine ⟨hGV, ?_⟩
  have hsub2 : Gcov ⌊A⌋₊ ⊆ (VA A)ᶜ ∪ (Gcov ⌊A⌋₊ ∩ VA A) := fun N hN => by
    by_cases h : N ∈ VA A
    · exact Or.inr ⟨hN, h⟩
    · exact Or.inl h
  have h1 := lowerDens_mono hsub2
  rw [lowerDens_union_of_densZero _ hGV, hV.compl.lowerDens_eq] at h1
  linarith


/-! ## The iterated logarithms and the parameter `P` -/

lemma logIt_one (x : ℝ) : logIt 1 x = Real.log x := rfl

lemma logIt_two (x : ℝ) : logIt 2 x = Real.log (Real.log x) := rfl

lemma logIt_three (x : ℝ) : logIt 3 x = Real.log (Real.log (Real.log x)) := rfl

/-- The regime `A ≥ e^{e^2}`: `log A ≥ e²`, `log log A ≥ 2`, `log log log A ≥ log 2`, and
`log log log A < log log A`. -/
lemma regime {A : ℝ} (hA : Real.exp (Real.exp 2) ≤ A) :
    Real.exp 2 ≤ Real.log A ∧ 2 ≤ Real.log (Real.log A) ∧
      Real.log 2 ≤ Real.log (Real.log (Real.log A)) ∧
      Real.log (Real.log (Real.log A)) < Real.log (Real.log A) := by
  have h1 : Real.exp 2 ≤ Real.log A := by
    have := Real.log_le_log (Real.exp_pos _) hA
    rwa [Real.log_exp] at this
  have h2 : 2 ≤ Real.log (Real.log A) := by
    have := Real.log_le_log (Real.exp_pos _) h1
    rwa [Real.log_exp] at this
  have h3 : Real.log 2 ≤ Real.log (Real.log (Real.log A)) := Real.log_le_log (by norm_num) h2
  have h4 := Real.log_le_sub_one_of_pos (show 0 < Real.log (Real.log A) by linarith)
  exact ⟨h1, h2, h3, by linarith⟩

lemma four_le_exp_exp_two : (4 : ℝ) ≤ Real.exp (Real.exp 2) := by
  have h1 : (2 : ℝ) + 1 ≤ Real.exp 2 := Real.add_one_le_exp 2
  have h2 : Real.exp 2 + 1 ≤ Real.exp (Real.exp 2) := Real.add_one_le_exp _
  linarith

/-- In the regime, all three iterated logarithms are positive. -/
lemma regime_pos {A : ℝ} (hA : Real.exp (Real.exp 2) ≤ A) :
    0 < logIt 1 A ∧ 0 < logIt 2 A ∧ 0 < logIt 3 A ∧ logIt 3 A < logIt 2 A := by
  obtain ⟨h1, h2, h3, h4⟩ := regime hA
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have he : (0 : ℝ) < Real.exp 2 := Real.exp_pos 2
  rw [logIt_one, logIt_two, logIt_three]
  exact ⟨by linarith, by linarith, by linarith, h4⟩

/-- The exponent `θ = 1 + (2 + (log₃ A)^{-1/2}) log₂ A / log₃ A` of `P = ⌊A^θ⌋`. -/
lemma two_le_theta {A : ℝ} (hA : Real.exp (Real.exp 2) ≤ A) :
    (2 : ℝ) ≤ 1 + (2 + 1 / Real.sqrt (logIt 3 A)) * logIt 2 A / logIt 3 A := by
  obtain ⟨_, h2, h3, h4⟩ := regime_pos hA
  have hs : 0 ≤ 1 / Real.sqrt (logIt 3 A) := by positivity
  have : 1 ≤ (2 + 1 / Real.sqrt (logIt 3 A)) * logIt 2 A / logIt 3 A := by
    rw [le_div_iff₀ h3]
    nlinarith
  linarith

lemma half_le_floor {x : ℝ} (hx : 1 ≤ x) : x / 2 ≤ (⌊x⌋₊ : ℝ) := by
  have h1 := Nat.lt_floor_add_one x
  have h2 : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast Nat.one_le_floor_iff x |>.2 hx
  linarith

lemma sq_le_rpow_theta {A : ℝ} (hA : Real.exp (Real.exp 2) ≤ A) :
    A ^ 2 ≤ A ^ (1 + (2 + 1 / Real.sqrt (logIt 3 A)) * logIt 2 A / logIt 3 A) := by
  have hA1 : 1 ≤ A := le_trans (by norm_num) (le_trans four_le_exp_exp_two hA)
  have := Real.rpow_le_rpow_of_exponent_le hA1 (two_le_theta hA)
  rwa [Real.rpow_two] at this

/-- `A < P` in the regime. -/
lemma lt_Pfix {A : ℝ} (hA : Real.exp (Real.exp 2) ≤ A) : A < (Pfix A : ℝ) := by
  have hA4 : 4 ≤ A := le_trans four_le_exp_exp_two hA
  have h1 := sq_le_rpow_theta hA
  have h2 := Nat.lt_floor_add_one (A ^ (1 + (2 + 1 / Real.sqrt (logIt 3 A)) * logIt 2 A /
    logIt 3 A))
  unfold Pfix
  nlinarith

/-- `A^θ / 2 ≤ P ≤ A^θ` in the regime. -/
lemma Pfix_bounds {A : ℝ} (hA : Real.exp (Real.exp 2) ≤ A) :
    A ^ (1 + (2 + 1 / Real.sqrt (logIt 3 A)) * logIt 2 A / logIt 3 A) / 2 ≤ (Pfix A : ℝ) ∧
      (Pfix A : ℝ) ≤ A ^ (1 + (2 + 1 / Real.sqrt (logIt 3 A)) * logIt 2 A / logIt 3 A) := by
  have hA4 : 4 ≤ A := le_trans four_le_exp_exp_two hA
  have h1 := sq_le_rpow_theta hA
  have h0 : 0 ≤ A ^ (1 + (2 + 1 / Real.sqrt (logIt 3 A)) * logIt 2 A / logIt 3 A) := by
    positivity
  unfold Pfix
  exact ⟨half_le_floor (by nlinarith), Nat.floor_le h0⟩

lemma tendsto_Pfix_atTop : Tendsto (fun A : ℝ => (Pfix A : ℝ)) atTop atTop := by
  refine tendsto_atTop_mono' atTop ?_ tendsto_id
  filter_upwards [eventually_ge_atTop (Real.exp (Real.exp 2))] with A hA
  exact (lt_Pfix hA).le

/-! ## `log P / B → 2`, with `B = log A · log log A / log log log A` -/

lemma tendsto_log_div_self : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
  have h := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  simpa using h

lemma tendsto_logIt_two : Tendsto (fun A : ℝ => logIt 2 A) atTop atTop :=
  Real.tendsto_log_atTop.comp Real.tendsto_log_atTop

lemma tendsto_logIt_three : Tendsto (fun A : ℝ => logIt 3 A) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_logIt_two

lemma tendsto_theta_div : Tendsto (fun A : ℝ => logIt 3 A / logIt 2 A + 2 +
    1 / Real.sqrt (logIt 3 A)) atTop (𝓝 2) := by
  have ha : Tendsto (fun A : ℝ => logIt 3 A / logIt 2 A) atTop (𝓝 0) :=
    tendsto_log_div_self.comp tendsto_logIt_two
  have hb : Tendsto (fun A : ℝ => 1 / Real.sqrt (logIt 3 A)) atTop (𝓝 0) := by
    have := tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_logIt_three)
    simpa [Function.comp_def, one_div] using this
  have := (ha.add (tendsto_const_nhds (x := (2 : ℝ)))).add hb
  simpa using this

lemma tendsto_B_atTop :
    Tendsto (fun A : ℝ => logIt 1 A * logIt 2 A / logIt 3 A) atTop atTop := by
  refine tendsto_atTop_mono' atTop ?_ Real.tendsto_log_atTop
  filter_upwards [eventually_ge_atTop (Real.exp (Real.exp 2))] with A hA
  obtain ⟨h1, h2, h3, h4⟩ := regime_pos hA
  rw [le_div_iff₀ h3, ← logIt_one]
  nlinarith

lemma tendsto_logPfix_div_B :
    Tendsto (fun A : ℝ => Real.log (Pfix A) / (logIt 1 A * logIt 2 A / logIt 3 A)) atTop
      (𝓝 2) := by
  have hf := tendsto_theta_div
  have hg : Tendsto (fun A : ℝ => logIt 3 A / logIt 2 A + 2 + 1 / Real.sqrt (logIt 3 A) -
      Real.log 2 / (logIt 1 A * logIt 2 A / logIt 3 A)) atTop (𝓝 2) := by
    have := hf.sub (Tendsto.div_atTop (tendsto_const_nhds (x := Real.log 2)) tendsto_B_atTop)
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hg hf ?_ ?_
  · filter_upwards [eventually_ge_atTop (Real.exp (Real.exp 2))] with A hA
    obtain ⟨h1, h2, h3, _⟩ := regime_pos hA
    have hA0 : 0 < A := lt_of_lt_of_le (Real.exp_pos _) hA
    have hB : 0 < logIt 1 A * logIt 2 A / logIt 3 A := by positivity
    have hs : 0 < Real.sqrt (logIt 3 A) := Real.sqrt_pos.2 h3
    obtain ⟨hlo, _⟩ := Pfix_bounds hA
    have hpow : 0 < A ^ (1 + (2 + 1 / Real.sqrt (logIt 3 A)) * logIt 2 A / logIt 3 A) := by
      positivity
    have hlog : Real.log (A ^ (1 + (2 + 1 / Real.sqrt (logIt 3 A)) * logIt 2 A /
        logIt 3 A)) - Real.log 2 ≤ Real.log (Pfix A) := by
      rw [← Real.log_div hpow.ne' (by norm_num)]
      exact Real.log_le_log (by positivity) hlo
    rw [Real.log_rpow hA0, ← logIt_one] at hlog
    have key : logIt 3 A / logIt 2 A + 2 + 1 / Real.sqrt (logIt 3 A) -
        Real.log 2 / (logIt 1 A * logIt 2 A / logIt 3 A) =
        ((1 + (2 + 1 / Real.sqrt (logIt 3 A)) * logIt 2 A / logIt 3 A) * logIt 1 A -
          Real.log 2) / (logIt 1 A * logIt 2 A / logIt 3 A) := by
      field_simp
      ring
    rw [key]
    exact div_le_div_of_nonneg_right hlog hB.le
  · filter_upwards [eventually_ge_atTop (Real.exp (Real.exp 2))] with A hA
    obtain ⟨h1, h2, h3, _⟩ := regime_pos hA
    have hA0 : 0 < A := lt_of_lt_of_le (Real.exp_pos _) hA
    have hB : 0 < logIt 1 A * logIt 2 A / logIt 3 A := by positivity
    have hs : 0 < Real.sqrt (logIt 3 A) := Real.sqrt_pos.2 h3
    obtain ⟨_, hhi⟩ := Pfix_bounds hA
    have hP0 : (0 : ℝ) < Pfix A := lt_trans hA0 (lt_Pfix hA)
    have hlog : Real.log (Pfix A) ≤ Real.log (A ^ (1 + (2 + 1 / Real.sqrt (logIt 3 A)) *
        logIt 2 A / logIt 3 A)) := Real.log_le_log hP0 hhi
    rw [Real.log_rpow hA0, ← logIt_one] at hlog
    have key : logIt 3 A / logIt 2 A + 2 + 1 / Real.sqrt (logIt 3 A) =
        ((1 + (2 + 1 / Real.sqrt (logIt 3 A)) * logIt 2 A / logIt 3 A) * logIt 1 A) /
          (logIt 1 A * logIt 2 A / logIt 3 A) := by
      field_simp
      ring
    rw [key]
    exact div_le_div_of_nonneg_right hlog hB.le

/-! ## `Claim_DeltaPfix` -/

theorem deltaPfix (hM3 : Std_Mertens3) : UpperTails.Claim_DeltaPfix := by
  intro ε hε
  have hQ := tendsto_logPfix_div_B
  have hP := tendsto_Pfix_atTop
  have hlogP : Tendsto (fun A : ℝ => Real.log (Pfix A)) atTop atTop :=
    Real.tendsto_log_atTop.comp hP
  have hM : Tendsto (fun A : ℝ => Delta (Pfix A) * Real.log (Pfix A)) atTop
      (𝓝 (Real.exp (-eulerGamma))) := hM3.comp hP
  have hinv : Tendsto (fun A : ℝ => (logIt 1 A * logIt 2 A / logIt 3 A) / Real.log (Pfix A))
      atTop (𝓝 2⁻¹) := by
    refine (hQ.inv₀ (by norm_num : (2 : ℝ) ≠ 0)).congr' ?_
    filter_upwards with A
    rw [inv_div]
  have hD : Tendsto (fun A : ℝ => Delta (Pfix A) / Lscale A) atTop
      (𝓝 (Real.exp (-eulerGamma) / 2)) := by
    have h := hM.mul hinv
    rw [← div_eq_mul_inv] at h
    refine h.congr' ?_
    filter_upwards [hlogP.eventually_gt_atTop 0, eventually_ge_atTop (Real.exp (Real.exp 2))]
      with A hlog hA
    obtain ⟨h1, h2, h3, _⟩ := regime_pos hA
    unfold Lscale
    field_simp
  have e1 := Metric.tendsto_nhds.1 hQ ε hε
  have e2 := Metric.tendsto_nhds.1 hD ε hε
  obtain ⟨A₀, hA₀⟩ := eventually_atTop.1 (e1.and (e2.and
    (eventually_ge_atTop (Real.exp (Real.exp 2)))))
  refine ⟨A₀, fun A hA => ?_⟩
  obtain ⟨h1, h2, hA'⟩ := hA₀ A hA
  obtain ⟨l1, l2, l3, _⟩ := regime_pos hA'
  rw [Real.dist_eq] at h1 h2
  have hB : 0 < logIt 1 A * logIt 2 A / logIt 3 A := by positivity
  have hL : 0 < Lscale A := by unfold Lscale; positivity
  constructor
  · have e : Real.log (Pfix A) - 2 * (logIt 1 A * logIt 2 A / logIt 3 A) =
        (logIt 1 A * logIt 2 A / logIt 3 A) *
          (Real.log (Pfix A) / (logIt 1 A * logIt 2 A / logIt 3 A) - 2) := by
      field_simp
    rw [e, abs_mul, abs_of_pos hB, mul_comm ε]
    exact mul_le_mul_of_nonneg_left h1.le hB.le
  · have e : Delta (Pfix A) - Real.exp (-eulerGamma) / 2 * Lscale A =
        Lscale A * (Delta (Pfix A) / Lscale A - Real.exp (-eulerGamma) / 2) := by
      field_simp
    rw [e, abs_mul, abs_of_pos hL, mul_comm ε]
    exact mul_le_mul_of_nonneg_left h2.le hL.le


/-! ## Densities of rough sets and of their multiples -/

lemma Delta_nonneg (y : ℝ) : 0 ≤ Delta y := by
  unfold Delta
  refine Finset.prod_nonneg fun p hp => ?_
  have hp2 := (Finset.mem_filter.1 hp).2.two_le
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast (by omega : 1 ≤ p)
  have : (1 : ℝ) / p ≤ 1 := by
    rw [div_le_one (by linarith)]
    exact hpR
  linarith

/-- For `n ≥ 1`, `y`-roughness is coprimality with `y#`. -/
lemma isRough_iff_coprime {y : ℝ} (hy : 0 ≤ y) {n : ℕ} (hn : n ≠ 0) :
    IsRough y n ↔ Nat.Coprime n (primorialR y) := by
  unfold IsRough primorialR
  constructor
  · intro h
    apply Nat.coprime_of_dvd
    intro p hp hpn hpP
    have h1 := h p (Nat.mem_primeFactors.2 ⟨hp, hpn, hn⟩)
    have h3 : (p : ℝ) ≤ y := (Nat.le_floor_iff hy).1 (hp.dvd_primorial_iff.1 hpP)
    linarith
  · intro h p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpn := Nat.dvd_of_mem_primeFactors hp
    by_contra hle
    have h2 : p ∣ primorial ⌊y⌋₊ := hpp.dvd_primorial_iff.2 (Nat.le_floor (not_lt.1 hle))
    exact hpp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes h hpn h2)

lemma cnt_congr_pos {S T : Set ℕ} (h : ∀ N, 1 ≤ N → (N ∈ S ↔ N ∈ T)) (X : ℝ) :
    cnt S X = cnt T X := by
  unfold cnt
  congr 1
  ext N
  rw [mem_cntFinset, mem_cntFinset]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, (h N h1.1).1 h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, (h N h1.1).2 h2⟩

/-- `y`-rough integers have density `Δ(y)` (from `Notation_Delta_density`). -/
lemma hasDens_rough (hDelta : Notation_Delta_density) {y : ℝ} (hy : 1 ≤ y) :
    HasDens {N : ℕ | IsRough y N} (Delta y) := by
  have h := (hDelta y hy).2
  unfold HasDens at h ⊢
  refine h.congr fun n => ?_
  rw [cnt_congr_pos (S := {N : ℕ | Nat.Coprime N (primorialR y)}) (T := {N : ℕ | IsRough y N})
    (fun N hN => (isRough_iff_coprime (by linarith) (by omega)).symm)]

lemma upperDens_biUnion_le {ι : Type*} [DecidableEq ι] (s : Finset ι) (B : ι → Set ℕ) :
    upperDens (⋃ i ∈ s, B i) ≤ ∑ i ∈ s, upperDens (B i) := by
  induction s using Finset.induction_on with
  | empty =>
    have h : (⋃ i ∈ (∅ : Finset ι), B i) = ∅ := by simp
    rw [h, Finset.sum_empty, densZero_empty.upperDens_eq]
  | insert a s ha ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert ha]
    exact (upperDens_union_le _ _).trans (by linarith)

open Classical in
/-- Dividing out a common factor `k`: if every `N ∈ T` is a multiple of `k` with `N / k ∈ R`, then
`cnt T (k X) ≤ cnt R X`. -/
lemma cnt_mul_le_of_div {T R : Set ℕ} {k : ℕ} (hk : 1 ≤ k)
    (h : ∀ N ∈ T, 1 ≤ N → k ∣ N ∧ N / k ∈ R) {X : ℝ} (hX : 0 ≤ X) :
    cnt T ((k : ℝ) * X) ≤ cnt R X := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  unfold cnt
  refine Finset.card_le_card_of_injOn (fun N => N / k) ?_ ?_
  · intro N hN
    rw [Finset.mem_coe, mem_cntFinset] at hN
    rw [Finset.mem_coe, mem_cntFinset]
    obtain ⟨⟨h1, h2⟩, hT⟩ := hN
    obtain ⟨hdvd, hR⟩ := h N hT h1
    refine ⟨⟨Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) (by omega), ?_⟩, hR⟩
    apply Nat.le_floor
    have hN : (N : ℝ) ≤ k * X := (Nat.le_floor_iff (by positivity)).1 h2
    rw [Nat.cast_div hdvd hkR.ne', div_le_iff₀ hkR]
    linarith
  · intro N₁ hN₁ N₂ hN₂ heq
    rw [Finset.mem_coe, mem_cntFinset] at hN₁ hN₂
    have h1 := (h N₁ hN₁.2 hN₁.1.1).1
    have h2 := (h N₂ hN₂.2 hN₂.1.1).1
    have heq' : N₁ / k = N₂ / k := heq
    rw [← Nat.div_mul_cancel h1, ← Nat.div_mul_cancel h2, heq']

lemma upperDens_le_div {T R : Set ℕ} {k : ℕ} (hk : 1 ≤ k)
    (h : ∀ N ∈ T, 1 ≤ N → k ∣ N ∧ N / k ∈ R) : upperDens T ≤ upperDens R / k := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hc : upperDens R < upperDens R + k * ε := by nlinarith
  obtain ⟨X₀, hX₀⟩ := exists_cnt_le_mul_of_upperDens_lt hc
  have hscaled : ∀ X : ℝ, max X₀ 0 ≤ X →
      (cnt T ((k : ℝ) * X) : ℝ) ≤ (upperDens R + k * ε) * X := by
    intro X hX
    have hX0 : 0 ≤ X := le_trans (le_max_right _ _) hX
    exact le_trans (by exact_mod_cast cnt_mul_le_of_div hk h hX0)
      (hX₀ X (le_trans (le_max_left _ _) hX))
  calc upperDens T ≤ (upperDens R + k * ε) / k := upperDens_le_of_scaled hkR hscaled
    _ = upperDens R / k + ε := by field_simp

/-- `P`-rough multiples of `k` have upper density at most `Δ(P)/k`. -/
lemma upperDens_rough_dvd_le (hDelta : Notation_Delta_density) {y : ℝ} (hy : 1 ≤ y) {k : ℕ}
    (hk : 1 ≤ k) : upperDens {N : ℕ | IsRough y N ∧ k ∣ N} ≤ Delta y / k := by
  rw [← (hasDens_rough hDelta hy).upperDens_eq]
  refine upperDens_le_div hk fun N hN hN1 => ⟨hN.2, ?_⟩
  intro p hp
  exact hN.1 p (Nat.primeFactors_mono (Nat.div_dvd_of_dvd hN.2) (by omega) hp)

/-! ## The `P`-rough moduli in `𝒦_A` -/

/-- `C(e, M) = ∑_{j < e, j ∣ M} M / j`: the value of `C` determined by `e` and `M`. -/
def psiC (M e : ℕ) : ℕ := ∑ j ∈ (Finset.Ico 1 e).filter (· ∣ M), M / j

lemma Csum_eq_psiC (e d : ℕ) : Csum e d = psiC (Mlcm e d) e := by
  unfold Csum psiC
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext j
  rw [mem_Dset, Finset.mem_filter, Finset.mem_Ico]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h2⟩, dvd_Mlcm (mem_Dset.2 ⟨h1, h2, h3⟩)⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, h2, h3.trans Mlcm_dvd⟩

lemma Csum_le (e d : ℕ) : Csum e d ≤ (e - 1) * Mlcm e d := by
  unfold Csum
  calc ∑ j ∈ Dset e d, Mlcm e d / j ≤ ∑ _j ∈ Dset e d, Mlcm e d :=
        Finset.sum_le_sum fun _ _ => Nat.div_le_self _ _
    _ = (Dset e d).card * Mlcm e d := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ (e - 1) * Mlcm e d := by
        apply Nat.mul_le_mul_right
        unfold Dset
        exact (Finset.card_filter_le _ _).trans (by rw [Nat.card_Ico])

open Classical in
/-- **The kernel count** (EP1054.tex lines 2045–2059). For `A ≥ 2` and `A < P`, every `P`-rough
modulus `k ∈ 𝒦_A` is `C(e, M)` for a divisor `e ∣ M` of some `M ∣ Λ(A)` with `M > P/A` and
`C ≥ M`; hence `∑ 1/k ≤ ∑_{M ∣ Λ(A), M > P/A} τ(M)/M = S(A, P/A)`. -/
lemma sum_inv_rough_moduli_le (hKG : Fact_KmodGeTwo) {A : ℝ} (hA : 2 ≤ A) {P : ℕ}
    (hAP : A < (P : ℝ)) :
    ∑ k ∈ (KAfin A).filter (fun k => IsRough (P : ℝ) k), (1 : ℝ) / k ≤
      Skernel A ((P : ℝ) / A) := by
  have hA0 : (0 : ℝ) < A := by linarith
  set Dv := (lcmUpTo A).divisors.filter (fun L : ℕ => (P : ℝ) / A < (L : ℝ)) with hDv
  set Pairs := Dv.sigma (fun M => M.divisors) with hPairs
  set Pairs' := Pairs.filter (fun q => q.1 ≤ psiC q.1 q.2) with hPairs'
  have hq1 : ∀ q ∈ Pairs, 0 < q.1 := fun q hq =>
    Nat.pos_of_mem_divisors (Finset.mem_filter.1 (Finset.mem_sigma.1 hq).1).1
  have hsub : (KAfin A).filter (fun k => IsRough (P : ℝ) k) ⊆
      Pairs'.image (fun q => psiC q.1 q.2) := by
    intro k hk
    rw [Finset.mem_filter] at hk
    obtain ⟨hkK, hkr⟩ := hk
    obtain ⟨e, d, ⟨he2, hea⟩, ⟨hd1, _⟩, rfl⟩ := mem_KAfin.1 hkK
    obtain ⟨_, hM0, _, hk2, hcase⟩ := hKG e d he2 hd1
    have hk0 : Kmod e d ≠ 0 := by omega
    have hsmall : ∀ p : ℕ, p.Prime → p ∣ Kmod e d → (P : ℝ) < p := fun p hp hpk =>
      hkr p (Nat.mem_primeFactors.2 ⟨hp, hpk, hk0⟩)
    have hg0 : 0 < Nat.gcd e (Mlcm e d) := Nat.gcd_pos_of_pos_left _ (by omega)
    have hgle : Nat.gcd e (Mlcm e d) ≤ e := Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left _ _)
    have heg : e / Nat.gcd e (Mlcm e d) = 1 := by
      by_contra hne
      have hpos : 0 < e / Nat.gcd e (Mlcm e d) := Nat.div_pos hgle hg0
      have hp := Nat.minFac_prime hne
      have hpk : Nat.minFac (e / Nat.gcd e (Mlcm e d)) ∣ Kmod e d :=
        (Nat.minFac_dvd _).trans (dvd_mul_right _ _)
      have hle : Nat.minFac (e / Nat.gcd e (Mlcm e d)) ≤ ⌊A⌋₊ :=
        (Nat.minFac_le hpos).trans ((Nat.div_le_self _ _).trans hea)
      have hleR : (Nat.minFac (e / Nat.gcd e (Mlcm e d)) : ℝ) ≤ A :=
        (Nat.le_floor_iff hA0.le).1 hle
      have := hsmall _ hp hpk
      linarith
    have hkC : Kmod e d = Csum e d := by
      unfold Kmod
      rw [heg, one_mul]
    obtain ⟨_, hMC⟩ := hcase heg
    have hgE : Nat.gcd e (Mlcm e d) = e := by
      have := Nat.div_mul_cancel (Nat.gcd_dvd_left e (Mlcm e d))
      rw [heg, one_mul] at this
      exact this
    have heDvd : e ∣ Mlcm e d := by
      have := Nat.gcd_dvd_right e (Mlcm e d)
      rwa [hgE] at this
    have hC2 : 2 ≤ Csum e d := by rw [← hkC]; exact hk2
    have hCP : (P : ℝ) < Csum e d := by
      have hp := Nat.minFac_prime (show Csum e d ≠ 1 by omega)
      have h1 := hsmall _ hp (by rw [hkC]; exact Nat.minFac_dvd _)
      have h2 : Nat.minFac (Csum e d) ≤ Csum e d := Nat.minFac_le (by omega)
      have : (Nat.minFac (Csum e d) : ℝ) ≤ Csum e d := by exact_mod_cast h2
      linarith
    have hMA : (P : ℝ) / A < Mlcm e d := by
      rw [div_lt_iff₀ hA0]
      have he1 : ((e - 1 : ℕ) : ℝ) ≤ A :=
        (Nat.le_floor_iff hA0.le).1 (le_trans (Nat.sub_le e 1) hea)
      have hCle : (Csum e d : ℝ) ≤ ((e - 1 : ℕ) : ℝ) * Mlcm e d := by
        exact_mod_cast Csum_le e d
      have hM0R : (0 : ℝ) ≤ Mlcm e d := Nat.cast_nonneg _
      nlinarith
    rw [Finset.mem_image]
    refine ⟨⟨Mlcm e d, e⟩, ?_, ?_⟩
    · rw [hPairs', Finset.mem_filter, hPairs, Finset.mem_sigma, hDv, Finset.mem_filter,
        Nat.mem_divisors, Nat.mem_divisors]
      refine ⟨⟨⟨⟨Mlcm_dvd_lcmUpTo hea, (lcmUpTo_pos A).ne'⟩, hMA⟩, heDvd, hM0.ne'⟩, ?_⟩
      show Mlcm e d ≤ psiC (Mlcm e d) e
      rw [← Csum_eq_psiC]
      exact hMC
    · show psiC (Mlcm e d) e = Kmod e d
      rw [← Csum_eq_psiC, hkC]
  calc ∑ k ∈ (KAfin A).filter (fun k => IsRough (P : ℝ) k), (1 : ℝ) / k
      ≤ ∑ k ∈ Pairs'.image (fun q => psiC q.1 q.2), (1 : ℝ) / k :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ ≤ ∑ q ∈ Pairs', (1 : ℝ) / (psiC q.1 q.2 : ℕ) :=
        Finset.sum_image_le_of_nonneg (fun _ _ => by positivity)
    _ ≤ ∑ q ∈ Pairs', (1 : ℝ) / q.1 := Finset.sum_le_sum fun q hq => by
        have h1 := (Finset.mem_filter.1 hq).2
        have h0 := hq1 q (Finset.mem_filter.1 hq).1
        exact one_div_le_one_div_of_le (by exact_mod_cast h0) (by exact_mod_cast h1)
    _ ≤ ∑ q ∈ Pairs, (1 : ℝ) / q.1 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => by positivity)
    _ = ∑ M ∈ Dv, ∑ _e ∈ M.divisors, (1 : ℝ) / M := Finset.sum_sigma _ _ _
    _ = Skernel A ((P : ℝ) / A) := by
        unfold Skernel
        refine Finset.sum_congr rfl fun M _ => ?_
        rw [Finset.sum_const, nsmul_eq_mul, mul_one_div]

/-! ## `Claim_RoughNotVA` -/

theorem roughNotVA (hKG : Fact_KmodGeTwo) (hK : UpperTails.Claim_KA_finite)
    (hDelta : Notation_Delta_density) : UpperTails.Claim_RoughNotVA := by
  classical
  refine ⟨Real.exp (Real.exp 2), fun A hA => ?_⟩
  have hA4 : 4 ≤ A := le_trans four_le_exp_exp_two hA
  have hA2 : 2 ≤ A := by linarith
  have hAP : A < (Pfix A : ℝ) := lt_Pfix hA
  have hP1 : (1 : ℝ) ≤ (Pfix A : ℝ) := by linarith
  have hsub : {N : ℕ | IsRough (Pfix A : ℝ) N ∧ N ∉ VA A} ⊆
      (⋃ k ∈ (KAfin A).filter (fun k => IsRough (Pfix A : ℝ) k),
        {N : ℕ | IsRough (Pfix A : ℝ) N ∧ k ∣ N}) ∪ {0} := by
    rintro N ⟨hNr, hNV⟩
    rcases Nat.eq_zero_or_pos N with h0 | hpos
    · exact Or.inr h0
    · left
      simp only [VA, Set.mem_setOf_eq, not_forall, not_not] at hNV
      obtain ⟨k, hkK, hkN⟩ := hNV
      rw [Set.mem_iUnion₂]
      refine ⟨k, Finset.mem_filter.2 ⟨(mem_KA_iff hK hA2).1 hkK, ?_⟩, hNr, hkN⟩
      intro p hp
      exact hNr p (Nat.primeFactors_mono hkN hpos.ne' hp)
  calc upperDens {N : ℕ | IsRough (Pfix A : ℝ) N ∧ N ∉ VA A}
      ≤ upperDens ((⋃ k ∈ (KAfin A).filter (fun k => IsRough (Pfix A : ℝ) k),
          {N : ℕ | IsRough (Pfix A : ℝ) N ∧ k ∣ N}) ∪ {0}) := upperDens_mono hsub
    _ = upperDens (⋃ k ∈ (KAfin A).filter (fun k => IsRough (Pfix A : ℝ) k),
          {N : ℕ | IsRough (Pfix A : ℝ) N ∧ k ∣ N}) :=
        upperDens_union_of_densZero _ (densZero_of_finite (Set.finite_singleton 0))
    _ ≤ ∑ k ∈ (KAfin A).filter (fun k => IsRough (Pfix A : ℝ) k),
          upperDens {N : ℕ | IsRough (Pfix A : ℝ) N ∧ k ∣ N} := upperDens_biUnion_le _ _
    _ ≤ ∑ k ∈ (KAfin A).filter (fun k => IsRough (Pfix A : ℝ) k),
          Delta (Pfix A : ℝ) * ((1 : ℝ) / k) := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hk2 := two_le_of_mem_KAfin hKG (Finset.mem_filter.1 hk).1
        rw [mul_one_div]
        exact upperDens_rough_dvd_le hDelta hP1 (by omega)
    _ = Delta (Pfix A : ℝ) * ∑ k ∈ (KAfin A).filter (fun k => IsRough (Pfix A : ℝ) k),
          (1 : ℝ) / k := by rw [Finset.mul_sum]
    _ ≤ Delta (Pfix A : ℝ) * Skernel A ((Pfix A : ℝ) / A) :=
        mul_le_mul_of_nonneg_left (sum_inv_rough_moduli_le hKG hA2 hAP) (Delta_nonneg _)

/-! ## `cor:fm-envelope-tail` -/

/-- The bound of `eq:fixed-kernel-tail` tends to `0`: its exponent is
`−(log₂/√log₃)(1 − C/√log₃) ≤ −√(log₂)/2` eventually. -/
lemma tendsto_kernel_bound (C : ℝ) :
    Tendsto (fun A : ℝ => Real.exp (-(logIt 2 A / Real.sqrt (logIt 3 A)) +
      C * (logIt 2 A / logIt 3 A))) atTop (𝓝 0) := by
  refine Real.tendsto_exp_atBot.comp ?_
  have hlim : Tendsto (fun A : ℝ => -(Real.sqrt (logIt 2 A) * (1 / 2))) atTop atBot :=
    tendsto_neg_atTop_atBot.comp
      ((Real.tendsto_sqrt_atTop.comp tendsto_logIt_two).atTop_mul_const (by norm_num))
  refine tendsto_atBot_mono' atTop ?_ hlim
  have hs := (Real.tendsto_sqrt_atTop.comp tendsto_logIt_three).eventually_ge_atTop (2 * |C|)
  filter_upwards [eventually_ge_atTop (Real.exp (Real.exp 2)), hs] with A hA hsA
  simp only [Function.comp_apply] at hsA
  obtain ⟨_, l2, l3, l32⟩ := regime_pos hA
  have hs0 : 0 < Real.sqrt (logIt 3 A) := Real.sqrt_pos.2 l3
  have ht0 : 0 ≤ Real.sqrt (logIt 2 A) := Real.sqrt_nonneg _
  have hst : Real.sqrt (logIt 3 A) ≤ Real.sqrt (logIt 2 A) := Real.sqrt_le_sqrt l32.le
  have hq0 : 0 ≤ logIt 2 A / Real.sqrt (logIt 3 A) := by positivity
  have hsplit : C * (logIt 2 A / logIt 3 A) =
      (C / Real.sqrt (logIt 3 A)) * (logIt 2 A / Real.sqrt (logIt 3 A)) := by
    have e : (C / Real.sqrt (logIt 3 A)) * (logIt 2 A / Real.sqrt (logIt 3 A)) =
        C * (logIt 2 A / (Real.sqrt (logIt 3 A) * Real.sqrt (logIt 3 A))) := by ring
    rw [e, Real.mul_self_sqrt l3.le]
  have hC : C / Real.sqrt (logIt 3 A) ≤ 1 / 2 := by
    rw [div_le_iff₀ hs0]
    have := le_abs_self C
    linarith
  have hge : Real.sqrt (logIt 2 A) ≤ logIt 2 A / Real.sqrt (logIt 3 A) := by
    rw [le_div_iff₀ hs0]
    calc Real.sqrt (logIt 2 A) * Real.sqrt (logIt 3 A)
        ≤ Real.sqrt (logIt 2 A) * Real.sqrt (logIt 2 A) := mul_le_mul_of_nonneg_left hst ht0
      _ = logIt 2 A := Real.mul_self_sqrt l2.le
  rw [hsplit]
  have := mul_le_mul_of_nonneg_right hC hq0
  linarith

theorem cor_fmEnvelopeTail (hVR : UpperTails.Claim_VA_rough) (hVD : UpperTails.Claim_VA_density)
    (hDelta : Notation_Delta_density) (hDP : UpperTails.Claim_DeltaPfix)
    (hRN : UpperTails.Claim_RoughNotVA) (hFK : Eq_FixedKernelTail) : Cor_FmEnvelopeTail := by
  refine ⟨?_, ⟨2, fun A hA => ?_⟩⟩
  · intro ε hε
    set c := Real.exp (-eulerGamma) / 2 with hcdef
    have hc : 0 < c := by positivity
    set δ := min 1 (ε / (2 * c)) with hδdef
    have hδ : 0 < δ := lt_min one_pos (by positivity)
    have hδ1 : δ ≤ 1 := min_le_left _ _
    have hδc : c * δ ≤ ε / 2 := by
      have h := min_le_right 1 (ε / (2 * c))
      rw [← hδdef] at h
      calc c * δ ≤ c * (ε / (2 * c)) := mul_le_mul_of_nonneg_left h hc.le
        _ = ε / 2 := by field_simp
    obtain ⟨C, E₀, hFKb⟩ := hFK
    obtain ⟨A₁, hA₁⟩ := eventually_atTop.1 ((tendsto_order.1 (tendsto_kernel_bound C)).2 δ hδ)
    obtain ⟨A₂, hA₂⟩ := hDP (ε / 2) (by linarith)
    obtain ⟨A₃, hA₃⟩ := hRN
    refine ⟨max (max A₁ A₂) (max (max A₃ E₀) (Real.exp (Real.exp 2))), fun A hA => ?_⟩
    have hA1 : A₁ ≤ A := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hA
    have hA2' : A₂ ≤ A := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hA
    have hA3 : A₃ ≤ A :=
      le_trans (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_right _ _))) hA
    have hAE : E₀ ≤ A :=
      le_trans (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_right _ _))) hA
    have hAe : Real.exp (Real.exp 2) ≤ A :=
      le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hA
    have hA4 : 4 ≤ A := le_trans four_le_exp_exp_two hAe
    have hA2 : 2 ≤ A := by linarith
    obtain ⟨l1, l2, l3, _⟩ := regime_pos hAe
    have hL : 0 ≤ Lscale A := by unfold Lscale; positivity
    have hP1 : (1 : ℝ) ≤ (Pfix A : ℝ) := by have := lt_Pfix hAe; linarith
    have hS : Skernel A ((Pfix A : ℝ) / A) ≤ δ := (hFKb A hAE).trans (hA₁ A hA1).le
    have hRNA := hA₃ A hA3
    have hDPA := (hA₂ A hA2').2
    have hV := (hVD A hA2).1
    have hCop := hasDens_rough hDelta hP1
    have hsub : {N : ℕ | IsRough (Pfix A : ℝ) N} ⊆
        {N : ℕ | IsRough (Pfix A : ℝ) N ∧ N ∉ VA A} ∪ VA A := fun N hN => by
      by_cases h : N ∈ VA A
      · exact Or.inr h
      · exact Or.inl ⟨hN, h⟩
    have h1 : Delta (Pfix A : ℝ) ≤
        upperDens {N : ℕ | IsRough (Pfix A : ℝ) N ∧ N ∉ VA A} + dV A := by
      rw [← hCop.lowerDens_eq, ← hV.lowerDens_eq]
      exact (lowerDens_mono hsub).trans (lowerDens_union_le _ _)
    have hD0 := Delta_nonneg (Pfix A : ℝ)
    have h2 : Delta (Pfix A : ℝ) * (1 - δ) ≤ dV A := by
      have := mul_le_mul_of_nonneg_left hS hD0
      nlinarith
    have h3 : (c - ε / 2) * Lscale A ≤ Delta (Pfix A : ℝ) := by
      have := (abs_le.1 hDPA).1
      rw [hcdef]
      linarith
    calc (Real.exp (-eulerGamma) / 2 - ε) * Lscale A
        ≤ (c - ε / 2) * Lscale A * (1 - δ) := by
          nlinarith [mul_nonneg hL (sub_nonneg.2 hδc), mul_nonneg hL (mul_nonneg hε.le hδ.le)]
      _ ≤ Delta (Pfix A : ℝ) * (1 - δ) := mul_le_mul_of_nonneg_right h3 (by linarith)
      _ ≤ dV A := h2
  · have hV := (hVD A hA).1
    have hR := hasDens_rough hDelta (by linarith : (1 : ℝ) ≤ A)
    rw [← hV.lowerDens_eq, ← hR.lowerDens_eq]
    exact lowerDens_mono fun N hN => (hVR A hA).2 N hN

end Principia.Erdos1054.Proofs.Envelope

/-! ## The obligations -/

namespace Principia.Erdos1054.Proofs

theorem link_UpperTails_Claim_KA_finite :
    Principia.Erdos1054.Spine.Link_UpperTails_Claim_KA_finite :=
  fun hFM _ => Envelope.kA_finite hFM

theorem link_UpperTails_Claim_VA_periodic :
    Principia.Erdos1054.Spine.Link_UpperTails_Claim_VA_periodic :=
  fun hK => Envelope.vA_periodic hK

theorem link_UpperTails_Claim_VA_density :
    Principia.Erdos1054.Spine.Link_UpperTails_Claim_VA_density :=
  fun hK _ hKG => Envelope.vA_density hK hKG

theorem leaf_UpperTails_Claim_VA_rough : Principia.Erdos1054.UpperTails.Claim_VA_rough :=
  Envelope.vA_rough

theorem link_Prop_FmEnvelope : Principia.Erdos1054.Spine.Link_Prop_FmEnvelope :=
  fun hSR hFM hFMN hK hVD => Envelope.prop_fmEnvelope hSR hFM hFMN hK hVD

theorem link_UpperTails_Claim_DeltaPfix :
    Principia.Erdos1054.Spine.Link_UpperTails_Claim_DeltaPfix :=
  fun hM3 => Envelope.deltaPfix hM3

theorem link_UpperTails_Claim_RoughNotVA :
    Principia.Erdos1054.Spine.Link_UpperTails_Claim_RoughNotVA :=
  fun _ hKG hK hDelta => Envelope.roughNotVA hKG hK hDelta

theorem link_Cor_FmEnvelopeTail : Principia.Erdos1054.Spine.Link_Cor_FmEnvelopeTail :=
  fun hVR hVD hDelta hDP hRN hFK => Envelope.cor_fmEnvelopeTail hVR hVD hDelta hDP hRN hFK

end Principia.Erdos1054.Proofs
