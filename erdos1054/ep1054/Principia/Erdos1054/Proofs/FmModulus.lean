/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Erdos1054.Spine
import Principia.Erdos1054.Density
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.Order.Group.DenselyOrdered

set_option autoImplicit false

/-!
# Erdős 1054 (EP1054.tex) — the exact forced modulus and the prime-cofactor ceiling

Proofs of the package `FmModulus` of `Campaigns/Erdos-1054/LEAN-WORKLIST.md`: paper lines 383–448
(the forced-modulus preamble, `lem:fm-modulus`, the rough-input remark) and 2443–2470 (the
prime-cofactor corollary, label `cor:fm-prime-ceiling` commented out in the source).

* `leaf_Fact_KmodGeTwo`, `leaf_Fact_DsetResidue` — the two preamble facts (no dependencies);
* `link_Fact_KmodFinite` — `K_{e,d}` is a function of `D ⊆ [1, e)`, so has finitely many values
  (the proof does not need the `Fact_DsetResidue` hypothesis the link carries);
* `link_Lem_FmModulus` — all four clauses, following lines 419–439 (the `Fact_KmodGeTwo`
  hypothesis is not consumed: `d₀ = M/g ≥ 1` is re-derived from `M > 0` here);
* `link_Rem_RoughInputModulus` — uses the criterion of `Fact_DsetResidue` and `Eq_FmCongruence`;
* `link_Cor_FmPrimeCeiling_congr`, `link_Cor_FmPrimeCeiling_count`,
  `link_Cor_FmPrimeCeiling_upperDens` — the three clauses of the corollary.

`Cor_FmPrimeCeiling` itself is the conjunction of its three clauses, assembled by `And.intro` in
the Spine; it has no `Link_` and is not declared here.
-/

namespace Principia.Erdos1054.Proofs.FmModulus

open Finset Principia.Erdos1054

/-! ## The objects `D`, `M`, `C`, `K` -/

lemma mem_Dset {e d j : ℕ} : j ∈ Dset e d ↔ 1 ≤ j ∧ j < e ∧ j ∣ e * d := by
  unfold Dset
  rw [Finset.mem_filter, Finset.mem_Ico, and_assoc]

lemma one_mem_Dset {e d : ℕ} (he : 2 ≤ e) : 1 ∈ Dset e d :=
  mem_Dset.2 ⟨le_rfl, by omega, one_dvd _⟩

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

lemma Mlcm_le_Csum {e d : ℕ} (he : 2 ≤ e) : Mlcm e d ≤ Csum e d := by
  unfold Csum
  calc Mlcm e d = Mlcm e d / 1 := (Nat.div_one _).symm
    _ ≤ ∑ j ∈ Dset e d, Mlcm e d / j :=
      Finset.single_le_sum (f := fun j => Mlcm e d / j) (fun j _ => Nat.zero_le _)
        (one_mem_Dset he)

lemma Mlcm_congr {e d d' : ℕ} (h : Dset e d = Dset e d') : Mlcm e d = Mlcm e d' := by
  unfold Mlcm
  rw [h]

lemma Csum_congr {e d d' : ℕ} (h : Dset e d = Dset e d') : Csum e d = Csum e d' := by
  unfold Csum
  rw [Mlcm_congr h, h]

lemma Kmod_congr {e d d' : ℕ} (h : Dset e d = Dset e d') : Kmod e d = Kmod e d' := by
  unfold Kmod
  rw [Mlcm_congr h, Csum_congr h]

/-- `n / M * (M / j) = n / j` for `j ∣ M ∣ n`, `M > 0`. -/
lemma div_mul_div_cancel' {n M j : ℕ} (hM : 0 < M) (hMn : M ∣ n) (hjM : j ∣ M) :
    n / M * (M / j) = n / j := by
  rw [Nat.div_mul_div_comm hMn hjM, mul_comm n M, Nat.mul_div_mul_left n j hM]

/-! ## `Fact_KmodGeTwo` -/

theorem kmodGeTwo : Fact_KmodGeTwo := by
  intro e d he _
  have hM := Mlcm_pos e d
  have hMC := Mlcm_le_Csum (d := d) he
  have hg0 : 0 < Nat.gcd e (Mlcm e d) := Nat.gcd_pos_of_pos_left _ (by omega)
  have hgle : Nat.gcd e (Mlcm e d) ≤ e := Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left _ _)
  have hq : 0 < e / Nat.gcd e (Mlcm e d) := Nat.div_pos hgle hg0
  have key : e / Nat.gcd e (Mlcm e d) = 1 → e ≤ Mlcm e d ∧ Mlcm e d ≤ Csum e d := by
    intro h1
    have hge : e = Nat.gcd e (Mlcm e d) := by
      have h2 := Nat.div_mul_cancel (Nat.gcd_dvd_left e (Mlcm e d))
      rw [h1, one_mul] at h2
      exact h2.symm
    exact ⟨hge.trans_le (Nat.le_of_dvd hM (Nat.gcd_dvd_right _ _)), hMC⟩
  refine ⟨one_mem_Dset he, hM, lt_of_lt_of_le hM hMC, ?_, key⟩
  unfold Kmod
  rcases Nat.lt_or_ge 1 (e / Nat.gcd e (Mlcm e d)) with h | h
  · have hC : 1 ≤ Csum e d := le_trans hM hMC
    have h2 : 2 ≤ e / Nat.gcd e (Mlcm e d) := h
    calc 2 = 2 * 1 := rfl
      _ ≤ e / Nat.gcd e (Mlcm e d) * Csum e d := Nat.mul_le_mul h2 hC
  · have h1 : e / Nat.gcd e (Mlcm e d) = 1 := by omega
    rw [h1, one_mul]
    have := (key h1).1
    omega

/-! ## `Fact_DsetResidue` -/

lemma dvd_mul_iff_div_gcd {j e d : ℕ} (hj : 0 < j) : j ∣ e * d ↔ j / Nat.gcd j e ∣ d := by
  have hpos : 0 < Nat.gcd j e := Nat.gcd_pos_of_pos_left e hj
  have hjj : j / Nat.gcd j e * Nat.gcd j e = j := Nat.div_mul_cancel (Nat.gcd_dvd_left j e)
  have hee : e / Nat.gcd j e * Nat.gcd j e = e := Nat.div_mul_cancel (Nat.gcd_dvd_right j e)
  constructor
  · intro hdvd
    have h1 : j / Nat.gcd j e * Nat.gcd j e ∣ e / Nat.gcd j e * d * Nat.gcd j e := by
      rw [hjj, mul_right_comm, hee]
      exact hdvd
    exact (Nat.coprime_div_gcd_div_gcd hpos).dvd_of_dvd_mul_left
      (Nat.dvd_of_mul_dvd_mul_right hpos h1)
  · intro hdvd
    have h1 := Nat.mul_dvd_mul_right hdvd (Nat.gcd j e)
    rw [hjj] at h1
    refine h1.trans ?_
    rw [mul_comm e d]
    exact Nat.mul_dvd_mul_left d (Nat.gcd_dvd_right j e)

lemma dvd_Dperiod {e j : ℕ} (h1 : 1 ≤ j) (h2 : j < e) : j / Nat.gcd j e ∣ Dperiod e :=
  Finset.dvd_lcm (f := fun j => j / Nat.gcd j e) (Finset.mem_Ico.2 ⟨h1, h2⟩)

theorem dsetResidue : Fact_DsetResidue := by
  intro e _
  refine ⟨fun j d hj _ => dvd_mul_iff_div_gcd (by omega), ?_⟩
  intro d d' _ _ hmod
  ext j
  rw [mem_Dset, mem_Dset]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, ?_⟩
    rw [dvd_mul_iff_div_gcd (by omega)] at h3 ⊢
    exact (hmod.dvd_iff (dvd_Dperiod h1 h2)).1 h3
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, ?_⟩
    rw [dvd_mul_iff_div_gcd (by omega)] at h3 ⊢
    exact (hmod.dvd_iff (dvd_Dperiod h1 h2)).2 h3

/-! ## `Fact_KmodFinite` -/

theorem kmodFinite : Fact_KmodFinite := by
  intro e _
  refine ((Finset.Ico 1 e).powerset.image (fun S : Finset ℕ =>
      e / Nat.gcd e (S.lcm id) * ∑ j ∈ S, S.lcm id / j)).finite_toSet.subset ?_
  rintro K ⟨d, _, rfl⟩
  rw [Finset.mem_coe, Finset.mem_image]
  refine ⟨Dset e d, ?_, rfl⟩
  rw [Finset.mem_powerset]
  exact Finset.filter_subset _ _

/-! ## `lem:fm-modulus` -/

lemma sigma_split (n d : ℕ) :
    sig n = ∑ r ∈ n.divisors.filter (· ≤ d), r +
      ∑ r ∈ n.divisors.filter (fun r => ¬ r ≤ d), r := by
  rw [sig, ArithmeticFunction.sigma_one_apply, Finset.sum_filter_add_sum_filter_not]

lemma div_le_iff_le {e d r : ℕ} (hd : 0 < d) (hr : r ∣ e * d) (hr0 : 0 < r) :
    e * d / r ≤ d ↔ e ≤ r := by
  have hmul : e * d / r * r = e * d := Nat.div_mul_cancel hr
  constructor
  · intro h
    have h1 : e * d / r * r ≤ d * r := Nat.mul_le_mul_right r h
    rw [hmul, mul_comm d r] at h1
    exact le_of_mul_le_mul_right h1 hd
  · intro h
    have h1 : e * d ≤ r * d := Nat.mul_le_mul_right d h
    rw [← hmul, mul_comm r d] at h1
    exact le_of_mul_le_mul_right h1 hr0

lemma Dset_eq_filter {e d : ℕ} (hn : e * d ≠ 0) : Dset e d = (e * d).divisors.filter (· < e) := by
  ext j
  rw [mem_Dset, Finset.mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨_, h2, h3⟩
    exact ⟨⟨h3, hn⟩, h2⟩
  · rintro ⟨⟨h3, _⟩, h2⟩
    exact ⟨Nat.pos_of_dvd_of_pos h3 (Nat.pos_of_ne_zero hn), h2, h3⟩

/-- The divisors of `n = e d` above `d` are the `n / j` with `j ∈ D`. -/
lemma sum_gt_eq {e d : ℕ} (he : 1 ≤ e) (hd : 1 ≤ d) :
    ∑ r ∈ (e * d).divisors.filter (fun r => ¬ r ≤ d), r = ∑ j ∈ Dset e d, e * d / j := by
  have hn : e * d ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
  rw [Finset.sum_filter, ← Nat.sum_div_divisors (e * d) (fun r => if ¬ r ≤ d then r else 0),
    Dset_eq_filter hn, Finset.sum_filter]
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [Nat.mem_divisors] at hr
  have hr0 : 0 < r := Nat.pos_of_dvd_of_pos hr.1 (Nat.pos_of_ne_zero hn)
  have hiff := div_le_iff_le hd hr.1 hr0
  by_cases h : e ≤ r
  · rw [if_neg (not_not.2 (hiff.2 h)), if_neg (not_lt.2 h)]
  · rw [if_pos (fun hc => h (hiff.1 hc)), if_pos (lt_of_not_ge h)]

lemma eq_fmReflection {e d : ℕ} (he : 1 ≤ e) (hd : 1 ≤ d) : Eq_FmReflection e d := by
  refine ⟨Mlcm_dvd, ?_⟩
  have h2 : ∑ j ∈ Dset e d, e * d / Mlcm e d * (Mlcm e d / j) = ∑ j ∈ Dset e d, e * d / j :=
    Finset.sum_congr rfl fun j hj => div_mul_div_cancel' (Mlcm_pos e d) Mlcm_dvd (dvd_Mlcm hj)
  rw [sigma_split (e * d) d, sum_gt_eq he hd, Csum, Finset.mul_sum, h2]
  rfl

lemma fm_divides {e d : ℕ} (he : 1 ≤ e) : Lem_FmModulus_Divides e d := by
  unfold Lem_FmModulus_Divides
  have hg : 0 < Nat.gcd e (Mlcm e d) := Nat.gcd_pos_of_pos_left _ he
  have hcop := (Nat.coprime_div_gcd_div_gcd hg).symm
  have hMe : Mlcm e d / Nat.gcd e (Mlcm e d) * Nat.gcd e (Mlcm e d) ∣
      e / Nat.gcd e (Mlcm e d) * d * Nat.gcd e (Mlcm e d) := by
    rw [Nat.div_mul_cancel (Nat.gcd_dvd_right e (Mlcm e d)), mul_right_comm,
      Nat.div_mul_cancel (Nat.gcd_dvd_left e (Mlcm e d))]
    exact Mlcm_dvd
  exact hcop.dvd_of_dvd_mul_left (Nat.dvd_of_mul_dvd_mul_right hg hMe)

lemma fm_congruence {e d : ℕ} (he : 1 ≤ e) (hd : 1 ≤ d) : Eq_FmCongruence e d := by
  unfold Eq_FmCongruence
  obtain ⟨hMn, hsum⟩ := eq_fmReflection he hd
  have hM := Mlcm_pos e d
  have hg : 0 < Nat.gcd e (Mlcm e d) := Nat.gcd_pos_of_pos_left _ he
  have hcop := Nat.coprime_div_gcd_div_gcd hg
  have hkey : e * d / Mlcm e d * (Mlcm e d / Nat.gcd e (Mlcm e d)) =
      e / Nat.gcd e (Mlcm e d) * d := by
    rw [div_mul_div_cancel' hM hMn (Nat.gcd_dvd_right e (Mlcm e d)),
      Nat.mul_div_right_comm (Nat.gcd_dvd_left e (Mlcm e d))]
  have hdvd : e / Nat.gcd e (Mlcm e d) ∣ e * d / Mlcm e d :=
    hcop.dvd_of_dvd_mul_right (hkey ▸ dvd_mul_right _ _)
  have hdiv : Kmod e d ∣ e * d / Mlcm e d * Csum e d := by
    unfold Kmod
    exact Nat.mul_dvd_mul_right hdvd (Csum e d)
  rw [← hsum]
  have h := (Nat.modEq_zero_iff_dvd.2 hdiv).symm.add_left (F e d)
  rwa [add_zero] at h

lemma fm_maximal {e d : ℕ} (he : 2 ≤ e) : Lem_FmModulus_Maximal e d := by
  refine ⟨fun d' hd' hD => ?_, fun K hK => ?_⟩
  · rw [← Kmod_congr hD]
    exact fm_congruence (by omega) hd'
  · have hM := Mlcm_pos e d
    have hg0 : 0 < Nat.gcd e (Mlcm e d) := Nat.gcd_pos_of_pos_left _ (by omega)
    have hgM : Nat.gcd e (Mlcm e d) ∣ Mlcm e d := Nat.gcd_dvd_right _ _
    have hge : Nat.gcd e (Mlcm e d) ∣ e := Nat.gcd_dvd_left _ _
    have hd0 : 1 ≤ Mlcm e d / Nat.gcd e (Mlcm e d) := Nat.div_pos (Nat.le_of_dvd hM hgM) hg0
    have hed0 : e * (Mlcm e d / Nat.gcd e (Mlcm e d)) =
        e / Nat.gcd e (Mlcm e d) * Mlcm e d := by
      rw [← Nat.mul_div_assoc e hgM, Nat.mul_div_right_comm hge]
    have hDd0 : Dset e (Mlcm e d / Nat.gcd e (Mlcm e d)) = Dset e d := by
      ext j
      rw [mem_Dset, mem_Dset]
      constructor
      · rintro ⟨h1, h2, h3⟩
        exact ⟨h1, h2, h3.trans (Nat.mul_dvd_mul_left e (fm_divides (by omega)))⟩
      · rintro ⟨h1, h2, h3⟩
        refine ⟨h1, h2, ?_⟩
        rw [hed0]
        exact (dvd_Mlcm (mem_Dset.2 ⟨h1, h2, h3⟩)).trans (dvd_mul_left _ _)
    have h0 := hK _ hd0 hDd0
    obtain ⟨_, hsum⟩ := eq_fmReflection (e := e) (by omega) hd0
    rw [← hsum, Mlcm_congr hDd0, Csum_congr hDd0, hed0, Nat.mul_div_cancel _ hM] at h0
    have h1 := (Nat.modEq_iff_dvd' (Nat.le_add_right _ _)).1 h0
    rw [Nat.add_sub_cancel_left] at h1
    exact h1

theorem fmModulus : Lem_FmModulus := fun e d he hd =>
  ⟨eq_fmReflection (by omega) hd, fm_divides (by omega), fm_congruence (by omega) hd,
    fm_maximal he⟩

/-! ## The rough-input remark -/

lemma sum_properDivisors_div {e : ℕ} (he : 1 ≤ e) :
    ∑ j ∈ e.properDivisors, e / j = sig e - 1 := by
  have h1 : sig e = ∑ j ∈ e.divisors, e / j := by
    rw [sig, ArithmeticFunction.sigma_one_apply]
    exact (Nat.sum_div_divisors e (fun j => j)).symm
  have h2 : ∑ j ∈ e.divisors, e / j = e / e + ∑ j ∈ e.properDivisors, e / j := by
    rw [← Nat.insert_self_properDivisors (by omega : e ≠ 0),
      Finset.sum_insert Nat.self_notMem_properDivisors]
  rw [Nat.div_self (by omega)] at h2
  omega

lemma Dset_rough {e d : ℕ} (hDR : Fact_DsetResidue) (he : 2 ≤ e) (hd : 1 ≤ d)
    (hP : ∀ p ∈ d.primeFactors, e ≤ p) : Dset e d = e.properDivisors := by
  ext j
  rw [mem_Dset, Nat.mem_properDivisors]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, h2⟩
    rw [(hDR e he).1 j d h1 h2] at h3
    have hg0 : 0 < Nat.gcd j e := Nat.gcd_pos_of_pos_left e (by omega)
    have hq : j / Nat.gcd j e = 1 := by
      by_contra hne
      obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
      have hpd : p ∈ d.primeFactors := Nat.mem_primeFactors.2 ⟨hp, hpdvd.trans h3, by omega⟩
      have hep := hP p hpd
      have hle : p ≤ j / Nat.gcd j e :=
        Nat.le_of_dvd (Nat.div_pos (Nat.gcd_le_left e (by omega)) hg0) hpdvd
      have hjle : j / Nat.gcd j e ≤ j := Nat.div_le_self _ _
      omega
    have hjg : j = Nat.gcd j e := by
      have h4 := Nat.div_mul_cancel (Nat.gcd_dvd_left j e)
      rw [hq, one_mul] at h4
      exact h4.symm
    rw [hjg]
    exact Nat.gcd_dvd_right j e
  · rintro ⟨h3, h2⟩
    exact ⟨Nat.pos_of_dvd_of_pos h3 (by omega), h2, h3.trans (dvd_mul_right e d)⟩

theorem roughInputModulus (hDR : Fact_DsetResidue) (hFM : Lem_FmModulus) :
    Rem_RoughInputModulus := by
  intro e d he hd hP
  have hD := Dset_rough hDR he hd hP
  have hM := Mlcm_pos e d
  have hMe : Mlcm e d ∣ e := by
    unfold Mlcm
    rw [hD]
    exact Finset.lcm_dvd fun _ hj => (Nat.mem_properDivisors.1 hj).1
  have hgcd : Nat.gcd e (Mlcm e d) = Mlcm e d := Nat.gcd_eq_right hMe
  have hK : Kmod e d = ∑ j ∈ e.properDivisors, e / j := by
    unfold Kmod Csum
    rw [hgcd, Finset.mul_sum, hD]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjD : j ∈ Dset e d := by
      rw [hD]
      exact hj
    exact div_mul_div_cancel' hM hMe (dvd_Mlcm hjD)
  have hK' : Kmod e d = sig e - 1 := hK.trans (sum_properDivisors_div (by omega))
  refine ⟨hD, hMe, hgcd, hK, hK', ?_⟩
  have h := (hFM e d he hd).2.2.1
  unfold Eq_FmCongruence at h
  rwa [hK'] at h

/-! ## The prime-cofactor corollary -/

theorem primeCeilingCongr (hFM : Lem_FmModulus) : Cor_FmPrimeCeiling_congr := by
  intro p hp d hd
  have hcong := (hFM p d hp.two_le hd).2.2.1
  refine Nat.ModEq.of_dvd ?_ hcong
  have hMfac : Mlcm p d ∣ Nat.factorial (p - 1) :=
    Finset.lcm_dvd fun j hj => show j ∣ Nat.factorial (p - 1) from
      Nat.dvd_factorial (mem_Dset.1 hj).1 (by have := (mem_Dset.1 hj).2.1; omega)
  have hpM : ¬ p ∣ Mlcm p d := fun h => by
    have h1 := (Nat.Prime.dvd_factorial hp).1 (h.trans hMfac)
    have h2 := hp.two_le
    omega
  have hg : Nat.gcd p (Mlcm p d) = 1 := (Nat.Prime.coprime_iff_not_dvd hp).2 hpM
  unfold Kmod
  rw [hg, Nat.div_one]
  exact dvd_mul_right p _

lemma cnt_Frange_sdiff_le (hcongr : Cor_FmPrimeCeiling_congr) (hFD : Disp_FinalDivisor)
    {p : ℕ} (hp : p.Prime) {X : ℝ} (hX : 0 ≤ X) :
    cnt (Frange p \ {N : ℕ | p ∣ N}) X ≤ cnt {n : ℕ | ¬ p ∣ sig n} ((p : ℝ) * X) := by
  unfold cnt
  refine le_trans (Finset.card_le_card ?_) (Finset.card_image_le (f := fun n => F p (n / p)))
  intro N hN
  rw [mem_cntFinset] at hN
  obtain ⟨⟨_, hNX⟩, ⟨d, hd, rfl⟩, hndvd⟩ := hN
  rw [Finset.mem_image]
  refine ⟨p * d, ?_, ?_⟩
  · rw [mem_cntFinset]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · have := Nat.mul_pos hp.pos hd
      omega
    · apply Nat.le_floor
      have hdF := (hFD p d hp.one_le hd).1
      have hdX : (d : ℝ) ≤ X :=
        le_trans (by exact_mod_cast hdF.trans hNX) (Nat.floor_le hX)
      push_cast
      exact mul_le_mul_of_nonneg_left hdX (Nat.cast_nonneg p)
    · intro hs
      exact hndvd (((hcongr p hp d hd).dvd_iff (dvd_refl p)).2 hs)
  · show F p (p * d / p) = F p d
    rw [Nat.mul_div_cancel_left d hp.pos]

theorem primeCeilingCount (hcongr : Cor_FmPrimeCeiling_congr) (hFD : Disp_FinalDivisor)
    (hFMN : Lem_FixedModulusNormality) : Cor_FmPrimeCeiling_count := by
  intro p hp ε hε
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  obtain ⟨Y₀, hY₀⟩ := DensZero.exists_le_mul (hFMN p hp.one_le) (div_pos hε hp0)
  refine ⟨max 0 (Y₀ / p), fun X hX => ?_⟩
  have hX0 : 0 ≤ X := le_trans (le_max_left _ _) hX
  have hpX : Y₀ ≤ p * X := by
    have h := le_trans (le_max_right _ _) hX
    rw [div_le_iff₀ hp0] at h
    linarith
  have h1 : (cnt (Frange p) X : ℝ) ≤
      cnt (Frange p \ {N : ℕ | p ∣ N}) X + cnt {N : ℕ | p ∣ N} X := by
    exact_mod_cast cnt_le_cnt_sdiff_add (Frange p) {N : ℕ | p ∣ N} X
  have h2 : (cnt {N : ℕ | p ∣ N} X : ℝ) ≤ X / p := cnt_dvd_le p hX0
  have h3 : (cnt (Frange p \ {N : ℕ | p ∣ N}) X : ℝ) ≤ cnt {n : ℕ | ¬ p ∣ sig n} ((p : ℝ) * X) := by
    exact_mod_cast cnt_Frange_sdiff_le hcongr hFD hp hX0
  have h4 := hY₀ ((p : ℝ) * X) hpX
  have h5 : ε / p * (p * X) = ε * X := by
    field_simp
  linarith

theorem primeCeilingUpperDens (hcount : Cor_FmPrimeCeiling_count) :
    Cor_FmPrimeCeiling_upperDens := by
  intro p hp
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨X₀, hX₀⟩ := hcount p hp ε hε
  refine upperDens_le_of_forall_ge (X₀ := X₀) fun X hX => ?_
  calc (cnt (Frange p) X : ℝ) ≤ X / p + ε * X := hX₀ X hX
    _ = (1 / p + ε) * X := by ring

end Principia.Erdos1054.Proofs.FmModulus

/-! ## The obligations of the package -/

namespace Principia.Erdos1054.Proofs

/-- `Fact_KmodGeTwo`, EP1054.tex line 393. -/
theorem leaf_Fact_KmodGeTwo : Principia.Erdos1054.Fact_KmodGeTwo :=
  FmModulus.kmodGeTwo

/-- `Fact_DsetResidue`, EP1054.tex lines 393–403. -/
theorem leaf_Fact_DsetResidue : Principia.Erdos1054.Fact_DsetResidue :=
  FmModulus.dsetResidue

/-- `Fact_KmodFinite`, EP1054.tex lines 404–405. -/
theorem link_Fact_KmodFinite : Principia.Erdos1054.Spine.Link_Fact_KmodFinite :=
  fun _ => FmModulus.kmodFinite

/-- `lem:fm-modulus`, EP1054.tex lines 406–440. -/
theorem link_Lem_FmModulus : Principia.Erdos1054.Spine.Link_Lem_FmModulus :=
  fun _ => FmModulus.fmModulus

/-- The rough-input remark, EP1054.tex lines 441–448. -/
theorem link_Rem_RoughInputModulus : Principia.Erdos1054.Spine.Link_Rem_RoughInputModulus :=
  fun hDR hFM => FmModulus.roughInputModulus hDR hFM

/-- Prime-cofactor corollary, congruence, EP1054.tex lines 2448–2450. -/
theorem link_Cor_FmPrimeCeiling_congr : Principia.Erdos1054.Spine.Link_Cor_FmPrimeCeiling_congr :=
  fun hFM => FmModulus.primeCeilingCongr hFM

/-- Prime-cofactor corollary, count, EP1054.tex lines 2451–2454. -/
theorem link_Cor_FmPrimeCeiling_count : Principia.Erdos1054.Spine.Link_Cor_FmPrimeCeiling_count :=
  fun hcongr hFD hFMN => FmModulus.primeCeilingCount hcongr hFD hFMN

/-- Prime-cofactor corollary, upper density, EP1054.tex line 2455. -/
theorem link_Cor_FmPrimeCeiling_upperDens :
    Principia.Erdos1054.Spine.Link_Cor_FmPrimeCeiling_upperDens :=
  fun hcount => FmModulus.primeCeilingUpperDens hcount

end Principia.Erdos1054.Proofs
