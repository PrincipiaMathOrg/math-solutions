/-
DEVELOPMENT — Erdős #361: the axiom-free modular-dichotomy engine (Alon 1987 Thm 1.1 is now
PROVED, not postulated — via general-h Dias da Silva–Hamidoune from Mathlib's Combinatorial
Nullstellensatz, restricted to the prime subsequence n = 2p), the avoider model, and the two
headline theorems `erdos361_irregular` (Thm 4) and `erdos361_cge1` (c ≥ 1 exact formula).
Imports the trusted `Erdos361.Statement` (its `Avoids`/`Avoiders`/`F`/`Fc`). No axioms beyond
the standard three.
-/
import Erdos361.Statement
set_option maxHeartbeats 4000000
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos361
open Erdos361.Statement MvPolynomial Finset Matrix Nat Filter Topology
open scoped Classical

variable {h p : ℕ}


/-- Falling-factorial Vandermonde determinant, over any integral domain `R`. -/
theorem det_descFactorial {R : Type*} [CommRing R] [IsDomain R] {h : ℕ} (d : Fin h → ℕ) :
    Matrix.det (Matrix.of fun i j => ((d i).descFactorial (j : ℕ) : R))
      = ∏ i : Fin h, ∏ j ∈ Finset.Ioi i, ((d j : R) - (d i : R)) := by
  set F : Matrix (Fin h) (Fin h) R := Matrix.of (fun i j => ((d i).descFactorial (j : ℕ) : R))
    with hFdef
  set V : Matrix (Fin h) (Fin h) R := Matrix.vandermonde (fun i => (d i : R)) with hV
  set M : Matrix (Fin h) (Fin h) R :=
    Matrix.of (fun l j => (descPochhammer R (j : ℕ)).coeff (l : ℕ)) with hM
  have hF : F = V * M := by
    ext i j
    rw [hFdef, Matrix.of_apply, Matrix.mul_apply]
    have hcast : ((d i).descFactorial (j : ℕ) : R) = (descPochhammer R (j : ℕ)).eval (d i : R) := by
      rw [descPochhammer_eval_eq_descFactorial]
    rw [hcast, Polynomial.eval_eq_sum_range' (n := h)
      (by rw [descPochhammer_natDegree]; exact j.2)]
    rw [← Fin.sum_univ_eq_sum_range (fun l => (descPochhammer R (j:ℕ)).coeff l * (d i : R) ^ l) h]
    apply Finset.sum_congr rfl
    intro l _
    rw [hV, hM, Matrix.of_apply, Matrix.vandermonde_apply]
    ring
  rw [hF, Matrix.det_mul]
  have hMdet : M.det = 1 := by
    rw [Matrix.det_of_upperTriangular]
    · apply Finset.prod_eq_one
      intro i _
      rw [hM, Matrix.of_apply]
      have hmon : (descPochhammer R (i : ℕ)).Monic := monic_descPochhammer R _
      have hnd : (descPochhammer R (i : ℕ)).natDegree = (i : ℕ) := descPochhammer_natDegree (R := R) _
      have hc := hmon.coeff_natDegree
      rwa [hnd] at hc
    · intro i j hji
      rw [hM, Matrix.of_apply]
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      rw [descPochhammer_natDegree (R := R)]
      exact hji
  rw [hMdet, mul_one, hV, Matrix.det_vandermonde]



lemma vand_perm :
    Matrix.det (Matrix.vandermonde (fun i => (X i : MvPolynomial (Fin h) (ZMod p))))
      = ∑ σ : Equiv.Perm (Fin h),
          ((Equiv.Perm.sign σ : ℤ) : MvPolynomial (Fin h) (ZMod p))
            * ∏ j, (X j) ^ ((σ j : Fin h) : ℕ) := by
  rw [Matrix.det_apply']
  refine Fintype.sum_equiv (Equiv.inv (Equiv.Perm (Fin h))) _ _ (fun σ => ?_)
  simp only [Equiv.inv_apply, Equiv.Perm.sign_inv]
  congr 1
  rw [← Equiv.prod_comp σ (fun j => (X j : MvPolynomial (Fin h) (ZMod p)) ^ ((σ⁻¹ j : Fin h) : ℕ))]
  apply Finset.prod_congr rfl
  intro i _
  rw [Matrix.vandermonde_apply]
  simp

/-- The monomial exponent vector for permutation `σ`: `uσ j = σ j`. -/
noncomputable def uperm (σ : Equiv.Perm (Fin h)) : Fin h →₀ ℕ :=
  Finsupp.indicator univ (fun i _ => ((σ i : Fin h) : ℕ))

lemma uperm_apply (σ : Equiv.Perm (Fin h)) (j : Fin h) : uperm σ j = ((σ j : Fin h) : ℕ) := by
  rw [uperm, Finsupp.indicator_apply]; simp

lemma coeff_vand_mul (P : MvPolynomial (Fin h) (ZMod p)) (t : Fin h →₀ ℕ) :
    coeff t (Matrix.det (Matrix.vandermonde fun i => (X i : MvPolynomial (Fin h) (ZMod p))) * P)
      = ∑ σ : Equiv.Perm (Fin h), ((Equiv.Perm.sign σ : ℤ) : ZMod p) *
          (if uperm σ ≤ t then coeff (t - uperm σ) P else 0) := by
  rw [vand_perm, Finset.sum_mul, coeff_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [mul_assoc,
    show ((Equiv.Perm.sign σ : ℤ) : MvPolynomial (Fin h) (ZMod p))
        = C ((Equiv.Perm.sign σ : ℤ) : ZMod p) from
      (map_intCast (MvPolynomial.C (σ := Fin h) (R := ZMod p)) _).symm,
    coeff_C_mul]
  congr 1
  rw [show (∏ j, (X j : MvPolynomial (Fin h) (ZMod p)) ^ ((σ j : Fin h) : ℕ)) = monomial (uperm σ) 1 by
    rw [uperm]; exact prod_X_pow _ _, coeff_monomial_mul']
  simp only [one_mul]




lemma multinomial_univ_spec (ν : Fin h →₀ ℕ) :
    ν.multinomial * ∏ i, (ν i)! = (ν.degree)! := by
  rw [Finsupp.multinomial_eq]
  have hprod : (∏ i, (ν i)!) = ∏ i ∈ ν.support, (ν i)! := by
    symm; apply Finset.prod_subset (Finset.subset_univ _)
    intro i _ hi; rw [Finsupp.notMem_support_iff.mp hi, Nat.factorial_zero]
  rw [hprod, Finsupp.degree, mul_comm]; exact Nat.multinomial_spec ν.support ν

lemma sum_perm_val (σ : Equiv.Perm (Fin h)) : ∑ i, ((σ i : Fin h) : ℕ) = ∑ i : Fin h, (i : ℕ) :=
  Equiv.sum_comp σ (fun i => (i : ℕ))

/-- Witness exponent vector `t i = (k-h)+i`. -/
noncomputable def twit (h k : ℕ) : Fin h →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun i => (k - h) + (i:ℕ))
lemma twit_apply (h k : ℕ) (i : Fin h) : twit h k i = (k - h) + (i:ℕ) := rfl

/-- **Per-permutation factorial identity.** -/
lemma per_sigma (k : ℕ) (hhk : h ≤ k) (σ : Equiv.Perm (Fin h)) :
    (if uperm σ ≤ twit h k then (twit h k - uperm σ).multinomial else 0) * ∏ i, ((twit h k) i)!
      = (h * (k - h))! * ∏ i, ((twit h k) i).descFactorial ((σ i : Fin h) : ℕ) := by
  by_cases hle : uperm σ ≤ twit h k
  · rw [if_pos hle]
    have hsle : ∀ i, ((σ i : Fin h) : ℕ) ≤ (twit h k) i := by
      intro i; have := hle i; rwa [uperm_apply] at this
    have hval : ∀ i, (twit h k - uperm σ) i = (twit h k) i - ((σ i : Fin h) : ℕ) := by
      intro i; rw [Finsupp.tsub_apply, uperm_apply]
    have hfac : ∀ i, ((twit h k) i)! = ((twit h k - uperm σ) i)! * ((twit h k) i).descFactorial ((σ i:Fin h):ℕ) := by
      intro i; rw [hval i, ← Nat.factorial_mul_descFactorial (hsle i)]
    have hdeg : (twit h k - uperm σ).degree = h * (k - h) := by
      rw [Finsupp.degree_eq_sum]
      set X := ∑ i : Fin h, (i:ℕ) with hX
      have hs2 : ∑ i, ((σ i:Fin h):ℕ) = X := sum_perm_val σ
      have hs3 : ∑ i : Fin h, (twit h k) i = h * (k - h) + X := by
        simp only [twit_apply]
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_fin, smul_eq_mul]
      have hadd : (∑ i, (twit h k - uperm σ) i) + ∑ i, ((σ i:Fin h):ℕ) = ∑ i : Fin h, (twit h k) i := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        rw [hval i]
        have := hsle i; omega
      omega
    calc (twit h k - uperm σ).multinomial * ∏ i, ((twit h k) i)!
        = (twit h k - uperm σ).multinomial *
            ∏ i, (((twit h k - uperm σ) i)! * ((twit h k) i).descFactorial ((σ i:Fin h):ℕ)) := by
          rw [Finset.prod_congr rfl (fun i _ => hfac i)]
      _ = ((twit h k - uperm σ).multinomial * ∏ i, ((twit h k - uperm σ) i)!)
            * ∏ i, ((twit h k) i).descFactorial ((σ i:Fin h):ℕ) := by
          rw [Finset.prod_mul_distrib]; ring
      _ = (h * (k - h))! * ∏ i, ((twit h k) i).descFactorial ((σ i:Fin h):ℕ) := by
          rw [multinomial_univ_spec, hdeg]
  · rw [if_neg hle, zero_mul]
    obtain ⟨i, hi⟩ : ∃ i, (twit h k) i < ((σ i:Fin h):ℕ) := by
      by_contra hc; push_neg at hc
      exact hle (fun i => by rw [uperm_apply]; exact hc i)
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (Nat.descFactorial_eq_zero_iff_lt.mpr hi), mul_zero]



/-- Bridge: the sum used by `coeff_sum_X_pow_of_fintype` is `Finsupp.degree`. -/
lemma sum_id_eq_degree (ν : Fin h →₀ ℕ) : ν.sum (fun _ m => m) = ν.degree := rfl

/-- `∏_{s∈H}((∑ᵢXᵢ) - C s) = (∑ᵢXᵢ)^|H| + low`, where `low` has zero coefficient in every
total degree `≥ |H|`. General-h version of the EH2 `prod_top`. -/
lemma prod_top (H : Finset (ZMod p)) :
    ∃ low : MvPolynomial (Fin h) (ZMod p),
      (∏ s ∈ H, ((∑ i, X i) - C s)) = (∑ i, X i) ^ H.card + low ∧
      ∀ μ : Fin h →₀ ℕ, H.card ≤ μ.degree → coeff μ low = 0 := by
  classical
  induction H using Finset.induction with
  | empty => exact ⟨0, by simp, by simp⟩
  | @insert s H' hs ih =>
    obtain ⟨low', hlow'eq, hlow'coeff⟩ := ih
    refine ⟨(∑ i, X i) * low' - C s * (∑ i, X i) ^ H'.card - C s * low', ?_, ?_⟩
    · rw [Finset.prod_insert hs, hlow'eq, Finset.card_insert_of_notMem hs]; ring
    · intro μ hμ
      rw [Finset.card_insert_of_notMem hs] at hμ   -- H'.card + 1 ≤ μ.degree
      rw [coeff_sub, coeff_sub]
      -- term 1: (∑X) * low'
      have ht1 : coeff μ ((∑ i, X i) * low') = 0 := by
        rw [Finset.sum_mul, coeff_sum]
        apply Finset.sum_eq_zero
        intro i _
        rw [coeff_X_mul']
        split_ifs with hi
        · apply hlow'coeff
          have hi1 : 1 ≤ μ i := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)
          have hle' : Finsupp.single i 1 ≤ μ := Finsupp.single_le_iff.mpr hi1
          have hcancel : (μ - Finsupp.single i 1) + Finsupp.single i 1 = μ :=
            tsub_add_cancel_of_le hle'
          have hdd := AddMonoidHom.map_add Finsupp.degree (μ - Finsupp.single i 1)
            (Finsupp.single i 1)
          rw [hcancel, Finsupp.degree_single] at hdd
          omega
        · rfl
      -- term 2: C s * (∑X)^|H'|
      have ht2 : coeff μ (C s * (∑ i, X i) ^ H'.card) = 0 := by
        rw [coeff_C_mul, coeff_sum_X_pow_of_fintype,
          if_neg (show ¬ (μ.sum (fun _ m => m) = H'.card) by
            rw [sum_id_eq_degree]; omega), Nat.cast_zero, mul_zero]
      -- term 3: C s * low'
      have ht3 : coeff μ (C s * low') = 0 := by
        rw [coeff_C_mul, hlow'coeff μ (by omega), mul_zero]
      rw [ht1, ht2, ht3]; ring

/-- Top-degree coefficient: for `μ` of degree `|H|`, `coeff μ (∏(∑X-Cs)) = μ.multinomial`. -/
lemma coeff_prod_top {H : Finset (ZMod p)} {μ : Fin h →₀ ℕ} (hμ : μ.degree = H.card) :
    coeff μ (∏ s ∈ H, ((∑ i, X i) - C s)) = (μ.multinomial : ZMod p) := by
  obtain ⟨low, hPeq, hlowc⟩ := prod_top H
  rw [hPeq, coeff_add, hlowc μ hμ.ge, add_zero, coeff_sum_X_pow_of_fintype,
    if_pos (show μ.sum (fun _ m => m) = H.card by rw [sum_id_eq_degree]; exact hμ)]


/-- (A) degree of the shifted witness. -/
lemma twit_sub_degree {h : ℕ} (k : ℕ) (σ : Equiv.Perm (Fin h)) (hle : uperm σ ≤ twit h k) :
    (twit h k - uperm σ).degree = h * (k - h) := by
  have hsle : ∀ i, ((σ i : Fin h) : ℕ) ≤ (twit h k) i := fun i => by
    have := hle i; rwa [uperm_apply] at this
  have hval : ∀ i, (twit h k - uperm σ) i = (twit h k) i - ((σ i : Fin h) : ℕ) := fun i => by
    rw [Finsupp.tsub_apply, uperm_apply]
  rw [Finsupp.degree_eq_sum]
  set X := ∑ i : Fin h, (i:ℕ) with hX
  have hs2 : ∑ i, ((σ i:Fin h):ℕ) = X := sum_perm_val σ
  have hs3 : ∑ i : Fin h, (twit h k) i = h * (k - h) + X := by
    simp only [twit_apply]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_fin, smul_eq_mul]
  have hadd : (∑ i, (twit h k - uperm σ) i) + ∑ i, ((σ i:Fin h):ℕ) = ∑ i : Fin h, (twit h k) i := by
    rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro i _; rw [hval i]
    have := hsle i; omega
  omega

/-- (B) the per-σ inner coefficient is the multinomial (cast), under the `≤` guard. -/
lemma coeff_sumpow_cast {h : ℕ} (k : ℕ) (σ : Equiv.Perm (Fin h)) :
    (if uperm σ ≤ twit h k then
        coeff (twit h k - uperm σ) ((∑ i, X i : MvPolynomial (Fin h) (ZMod p)) ^ (h * (k - h)))
      else 0)
      = (((if uperm σ ≤ twit h k then (twit h k - uperm σ).multinomial else 0) : ℕ) : ZMod p) := by
  by_cases hle : uperm σ ≤ twit h k
  · simp only [if_pos hle]
    rw [coeff_sum_X_pow_of_fintype,
      if_pos (show (twit h k - uperm σ).sum (fun _ m => m) = h * (k - h) by
        rw [sum_id_eq_degree]; exact twit_sub_degree k σ hle)]
  · rw [if_neg hle, if_neg hle, Nat.cast_zero]

/-- (D) the signed permutation sum of descFactorials is the falling-factorial determinant. -/
lemma det_perm_sum {h : ℕ} [Fact p.Prime] (k : ℕ) :
    (∑ σ : Equiv.Perm (Fin h), ((Equiv.Perm.sign σ : ℤ) : ZMod p) *
        ∏ i, (((twit h k) i).descFactorial ((σ i : Fin h) : ℕ) : ZMod p))
      = ∏ i, ∏ j ∈ Ioi i, ((twit h k j : ZMod p) - (twit h k i : ZMod p)) := by
  rw [← det_descFactorial (R := ZMod p) (fun i => twit h k i), ← Matrix.det_transpose,
    Matrix.det_apply']
  apply Finset.sum_congr rfl
  intro σ _
  simp only [Matrix.transpose_apply, Matrix.of_apply]

/-- (C–E) The witness coefficient of `vand·(∑X)^m` is nonzero mod `p`. -/
lemma coeff_top_ne_zero {h k : ℕ} [Fact p.Prime]
    (hh : 1 ≤ h) (hhk : h ≤ k) (hkp : k ≤ p) (hmp : h * (k - h) < p) :
    coeff (twit h k) (Matrix.det (Matrix.vandermonde (fun i => (X i : MvPolynomial (Fin h) (ZMod p))))
        * (∑ i, X i) ^ (h * (k - h))) ≠ 0 := by
  have hident :
      coeff (twit h k) (Matrix.det (Matrix.vandermonde (fun i => (X i : MvPolynomial (Fin h) (ZMod p))))
          * (∑ i, X i) ^ (h * (k - h))) * ∏ i, ((twit h k i)! : ZMod p)
        = ((h * (k - h))! : ZMod p) * ∏ i, ∏ j ∈ Ioi i, ((twit h k j : ZMod p) - twit h k i) := by
    rw [coeff_vand_mul, Finset.sum_mul, ← det_perm_sum k, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    rw [coeff_sumpow_cast]
    have hkey : (((if uperm σ ≤ twit h k then (twit h k - uperm σ).multinomial else 0 : ℕ)) : ZMod p)
          * ∏ i, ((twit h k i)! : ZMod p)
        = ((h * (k - h))! : ZMod p) * ∏ i, (((twit h k i).descFactorial ((σ i:Fin h):ℕ)) : ZMod p) := by
      rw [← Nat.cast_prod, ← Nat.cast_mul, per_sigma k hhk σ, Nat.cast_mul, Nat.cast_prod]
    linear_combination ((Equiv.Perm.sign σ : ℤ) : ZMod p) * hkey
  intro hC0
  rw [hC0, zero_mul] at hident
  -- RHS ≠ 0
  have hfac_ne : ((h * (k - h))! : ZMod p) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff (ZMod p) p, (inferInstance : Fact p.Prime).out.dvd_factorial]
    omega
  have hprod_ne : (∏ i : Fin h, ∏ j ∈ Ioi i, ((twit h k j : ZMod p) - twit h k i)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro i _
    rw [Finset.prod_ne_zero_iff]
    intro j hj
    rw [sub_ne_zero, Ne]
    intro heq
    have hji : i < j := Finset.mem_Ioi.mp hj
    have hji' : (i:ℕ) < (j:ℕ) := hji
    have hib : (twit h k i) < p := by rw [twit_apply]; omega
    have hjb : (twit h k j) < p := by rw [twit_apply]; omega
    have : twit h k j = twit h k i := by
      have h1 : ((twit h k j : ZMod p)).val = ((twit h k i : ZMod p)).val := by rw [heq]
      rwa [ZMod.val_natCast_of_lt hjb, ZMod.val_natCast_of_lt hib] at h1
    rw [twit_apply, twit_apply] at this
    omega
  exact (mul_ne_zero hfac_ne hprod_ne) hident.symm

/-- restricted h-sumset. -/
noncomputable def rsumH (h : ℕ) (A : Finset (ZMod p)) : Finset (ZMod p) :=
  (A.powersetCard h).image (fun s => s.sum id)

/-- (F) vanishing of the DSH polynomial (det form) on `A^h`. -/
lemma dshPoly_vanish {h : ℕ} [Fact p.Prime] {A H : Finset (ZMod p)} (hHA : rsumH h A ⊆ H)
    (s : Fin h → ZMod p) (hs : ∀ i, s i ∈ A) :
    eval s (Matrix.det (Matrix.vandermonde (fun i => (X i : MvPolynomial (Fin h) (ZMod p))))
        * ∏ c ∈ H, ((∑ i, X i) - C c)) = 0 := by
  rw [eval_mul]
  by_cases hinj : Function.Injective s
  · have himg : (univ.image s).card = h := by
      rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
    have hsub : univ.image s ⊆ A := by
      intro a ha; rw [mem_image] at ha; obtain ⟨i, _, rfl⟩ := ha; exact hs i
    have hmem : (univ.image s).sum id ∈ rsumH h A := by
      rw [rsumH, mem_image]; exact ⟨univ.image s, by rw [mem_powersetCard]; exact ⟨hsub, himg⟩, rfl⟩
    have hsum : (∑ i, s i) = (univ.image s).sum id := by
      rw [Finset.sum_image (fun i _ j _ hij => hinj hij)]; rfl
    have : eval s (∏ c ∈ H, ((∑ i, X i) - C c)) = 0 := by
      rw [eval_prod]; apply Finset.prod_eq_zero (hHA (hsum ▸ hmem)); simp
    rw [this, mul_zero]
  · have hz : eval s (Matrix.det (Matrix.vandermonde (fun i => (X i : MvPolynomial (Fin h) (ZMod p))))) = 0 := by
      rw [RingHom.map_det]
      have hmap : (MvPolynomial.eval s).mapMatrix (Matrix.vandermonde (fun i => (X i : MvPolynomial (Fin h) (ZMod p))))
          = Matrix.vandermonde s := by
        ext i j; simp [RingHom.mapMatrix_apply, Matrix.vandermonde_apply]
      rw [hmap, Matrix.det_vandermonde_eq_zero_iff]
      rw [Function.not_injective_iff] at hinj
      obtain ⟨a, b, hab, hne⟩ := hinj
      exact ⟨a, b, hab, hne⟩
    rw [hz, zero_mul]

/-- **General-h Dias da Silva–Hamidoune bound** (axiom-free replacement for Alon). -/
theorem dsh {h : ℕ} [Fact p.Prime] (A : Finset (ZMod p)) (hh : 1 ≤ h) (hhA : h ≤ A.card)
    (hp : h * (A.card - h) + 1 ≤ p) :
    h * (A.card - h) + 1 ≤ (rsumH h A).card := by
  by_contra hlt
  push_neg at hlt
  set k := A.card with hk
  have hcardp : Fintype.card (ZMod p) = p := ZMod.card p
  obtain ⟨H, hHsub, hHcard⟩ : ∃ H : Finset (ZMod p), rsumH h A ⊆ H ∧ H.card = h * (k - h) :=
    Finset.exists_superset_card_eq (by omega) (by rw [hcardp]; omega)
  have hkp : k ≤ p := by rw [← hcardp]; exact Finset.card_le_univ A
  -- coefficient of the witness monomial is nonzero
  have hcoeff : coeff (twit h k) (Matrix.det (Matrix.vandermonde (fun i => (X i : MvPolynomial (Fin h) (ZMod p))))
      * ∏ c ∈ H, ((∑ i, X i) - C c)) ≠ 0 := by
    -- = coeff of vand·(∑X)^m  (low part contributes 0)
    obtain ⟨low, hPeq, hlowc⟩ := prod_top (h := h) H
    rw [hPeq, mul_add, coeff_add, hHcard]
    have hlow0 : coeff (twit h k) (Matrix.det (Matrix.vandermonde (fun i => (X i : MvPolynomial (Fin h) (ZMod p)))) * low) = 0 := by
      rw [coeff_vand_mul]
      apply Finset.sum_eq_zero
      intro σ _
      by_cases hle : uperm σ ≤ twit h k
      · rw [if_pos hle, hlowc _ (le_of_eq (by rw [hHcard, twit_sub_degree k σ hle])), mul_zero]
      · rw [if_neg hle, mul_zero]
    rw [hlow0, add_zero]
    exact coeff_top_ne_zero hh hhA hkp (by omega)
  -- total degree
  have hdeg_eq : (twit h k).degree = (∑ i : Fin h, (i:ℕ)) + h * (k - h) := by
    rw [Finsupp.degree_eq_sum]; simp only [twit_apply]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_fin, smul_eq_mul]; ring
  have htd : (Matrix.det (Matrix.vandermonde (fun i => (X i : MvPolynomial (Fin h) (ZMod p))))
      * ∏ c ∈ H, ((∑ i, X i) - C c)).totalDegree = (twit h k).degree := by
    refine le_antisymm ?_ (MvPolynomial.le_totalDegree (s := twit h k) (by simpa using hcoeff))
    refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
    have hv : (Matrix.det (Matrix.vandermonde (fun i => (X i : MvPolynomial (Fin h) (ZMod p))))).totalDegree
        ≤ ∑ i : Fin h, (i:ℕ) := by
      rw [vand_perm]
      refine le_trans (MvPolynomial.totalDegree_finset_sum _ _) (Finset.sup_le ?_)
      intro σ _
      refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
      have h1 : ((Equiv.Perm.sign σ : ℤ) : MvPolynomial (Fin h) (ZMod p)).totalDegree = 0 := by
        rw [← map_intCast (MvPolynomial.C (σ := Fin h) (R := ZMod p))]; exact MvPolynomial.totalDegree_C _
      have h2 : (∏ j, (X j : MvPolynomial (Fin h) (ZMod p)) ^ ((σ j : Fin h):ℕ)).totalDegree
          ≤ ∑ i : Fin h, (i:ℕ) := by
        refine le_trans (MvPolynomial.totalDegree_finset_prod _ _) ?_
        rw [← sum_perm_val σ]
        apply Finset.sum_le_sum
        intro j _
        exact le_trans (MvPolynomial.totalDegree_pow _ _) (le_of_eq (by rw [MvPolynomial.totalDegree_X, mul_one]))
      rw [h1]; omega
    have hp2 : (∏ c ∈ H, ((∑ i, X i : MvPolynomial (Fin h) (ZMod p)) - C c)).totalDegree ≤ h*(k-h) := by
      refine le_trans (MvPolynomial.totalDegree_finset_prod _ _) ?_
      refine le_trans (Finset.sum_le_sum (fun c _ => ?_)) (by rw [Finset.sum_const, hHcard, smul_eq_mul, mul_one])
      refine le_trans (MvPolynomial.totalDegree_sub _ _) (max_le ?_ ?_)
      · exact le_trans (MvPolynomial.totalDegree_finset_sum _ _)
          (Finset.sup_le (fun i _ => by rw [MvPolynomial.totalDegree_X]))
      · rw [MvPolynomial.totalDegree_C]; exact Nat.zero_le _
    rw [hdeg_eq]; omega
  -- each exponent < k
  have hS : ∀ i, (twit h k) i < k := by
    intro i; rw [twit_apply]; omega
  obtain ⟨s, hsA, hne⟩ :=
    combinatorial_nullstellensatz_exists_eval_nonzero _ (twit h k) hcoeff htd (fun _ => A) hS
  exact hne (dshPoly_vanish hHsub s hsA)

/-- General witness exponent vector for an arbitrary `d`. -/
noncomputable def tg {h : ℕ} (d : Fin h → ℕ) : Fin h →₀ ℕ := Finsupp.equivFunOnFinite.symm d
lemma tg_apply {h : ℕ} (d : Fin h → ℕ) (i : Fin h) : tg d i = d i := rfl
/-- degree of the general witness minus the "staircase". -/
def Mdeg {h : ℕ} (d : Fin h → ℕ) : ℕ := (∑ i : Fin h, d i) - (∑ i : Fin h, (i:ℕ))

lemma tg_sub_degree_gen {h : ℕ} (d : Fin h → ℕ) (hge : ∀ i : Fin h, (i:ℕ) ≤ d i)
    (σ : Equiv.Perm (Fin h)) (hle : uperm σ ≤ tg d) : (tg d - uperm σ).degree = Mdeg d := by
  have hsle : ∀ i, ((σ i : Fin h) : ℕ) ≤ (tg d) i := fun i => by
    have := hle i; rwa [uperm_apply] at this
  have hval : ∀ i, (tg d - uperm σ) i = (tg d) i - ((σ i : Fin h) : ℕ) := fun i => by
    rw [Finsupp.tsub_apply, uperm_apply]
  rw [Finsupp.degree_eq_sum, Mdeg]
  set X := ∑ i : Fin h, (i:ℕ) with hX
  have hs2 : ∑ i, ((σ i:Fin h):ℕ) = X := sum_perm_val σ
  have hs3 : ∑ i : Fin h, (tg d) i = ∑ i : Fin h, d i := by simp only [tg_apply]
  have hgeX : X ≤ ∑ i : Fin h, d i := by rw [hX]; exact Finset.sum_le_sum (fun i _ => hge i)
  have hadd : (∑ i, (tg d - uperm σ) i) + ∑ i, ((σ i:Fin h):ℕ) = ∑ i : Fin h, (tg d) i := by
    rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro i _; rw [hval i]
    have := hsle i; omega
  omega

lemma per_sigma_gen {h : ℕ} (d : Fin h → ℕ) (hge : ∀ i : Fin h, (i:ℕ) ≤ d i) (σ : Equiv.Perm (Fin h)) :
    (if uperm σ ≤ tg d then (tg d - uperm σ).multinomial else 0) * ∏ i : Fin h, ((d i)!)
      = (Mdeg d)! * ∏ i, (d i).descFactorial ((σ i : Fin h) : ℕ) := by
  by_cases hle : uperm σ ≤ tg d
  · rw [if_pos hle]
    have hsle : ∀ i, ((σ i : Fin h) : ℕ) ≤ d i := fun i => by
      have := hle i; rwa [uperm_apply] at this
    have hval : ∀ i, (tg d - uperm σ) i = d i - ((σ i : Fin h) : ℕ) := fun i => by
      rw [Finsupp.tsub_apply, uperm_apply, tg_apply]
    have hfac : ∀ i, (d i)! = ((tg d - uperm σ) i)! * (d i).descFactorial ((σ i:Fin h):ℕ) := by
      intro i; rw [hval i, ← Nat.factorial_mul_descFactorial (hsle i)]
    calc (tg d - uperm σ).multinomial * ∏ i : Fin h, ((d i)!)
        = (tg d - uperm σ).multinomial *
            ∏ i : Fin h, (((tg d - uperm σ) i)! * (d i).descFactorial ((σ i:Fin h):ℕ)) := by
          rw [Finset.prod_congr rfl (fun i _ => hfac i)]
      _ = ((tg d - uperm σ).multinomial * ∏ i : Fin h, ((tg d - uperm σ) i)!)
            * ∏ i, (d i).descFactorial ((σ i:Fin h):ℕ) := by rw [Finset.prod_mul_distrib]; ring
      _ = (Mdeg d)! * ∏ i, (d i).descFactorial ((σ i:Fin h):ℕ) := by
          rw [multinomial_univ_spec, tg_sub_degree_gen d hge σ hle]
  · rw [if_neg hle, zero_mul]
    obtain ⟨i, hi⟩ : ∃ i, d i < ((σ i:Fin h):ℕ) := by
      by_contra hc; push_neg at hc
      exact hle (fun i => by rw [uperm_apply, tg_apply]; exact hc i)
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (Nat.descFactorial_eq_zero_iff_lt.mpr hi), mul_zero]

lemma coeff_sumpow_cast_gen {h : ℕ} (d : Fin h → ℕ) (hge : ∀ i : Fin h, (i:ℕ) ≤ d i)
    (σ : Equiv.Perm (Fin h)) :
    (if uperm σ ≤ tg d then
        coeff (tg d - uperm σ) ((∑ i, X i : MvPolynomial (Fin h) (ZMod p)) ^ (Mdeg d)) else 0)
      = (((if uperm σ ≤ tg d then (tg d - uperm σ).multinomial else 0) : ℕ) : ZMod p) := by
  by_cases hle : uperm σ ≤ tg d
  · simp only [if_pos hle]
    rw [coeff_sum_X_pow_of_fintype,
      if_pos (show (tg d - uperm σ).sum (fun _ m => m) = Mdeg d by
        rw [sum_id_eq_degree]; exact tg_sub_degree_gen d hge σ hle)]
  · rw [if_neg hle, if_neg hle, Nat.cast_zero]

lemma det_perm_sum_gen {h : ℕ} [Fact p.Prime] (d : Fin h → ℕ) :
    (∑ σ : Equiv.Perm (Fin h), ((Equiv.Perm.sign σ : ℤ) : ZMod p) *
        ∏ i : Fin h, ((d i).descFactorial ((σ i : Fin h) : ℕ) : ZMod p))
      = ∏ i, ∏ j ∈ Ioi i, ((d j : ZMod p) - (d i : ZMod p)) := by
  rw [← det_descFactorial (R := ZMod p) d, ← Matrix.det_transpose, Matrix.det_apply']
  apply Finset.sum_congr rfl
  intro σ _
  simp only [Matrix.transpose_apply, Matrix.of_apply]

lemma coeff_top_ne_zero_gen {h : ℕ} [Fact p.Prime] (d : Fin h → ℕ)
    (hge : ∀ i : Fin h, (i:ℕ) ≤ d i) (hinj : Function.Injective d) (hlt : ∀ i : Fin h, d i < p) (hMp : Mdeg d < p) :
    coeff (tg d) (Matrix.det (Matrix.vandermonde (fun i => (X i : MvPolynomial (Fin h) (ZMod p))))
        * (∑ i, X i) ^ (Mdeg d)) ≠ 0 := by
  have hident :
      coeff (tg d) (Matrix.det (Matrix.vandermonde (fun i => (X i : MvPolynomial (Fin h) (ZMod p))))
          * (∑ i, X i) ^ (Mdeg d)) * ∏ i : Fin h, ((d i)! : ZMod p)
        = ((Mdeg d)! : ZMod p) * ∏ i, ∏ j ∈ Ioi i, ((d j : ZMod p) - d i) := by
    rw [coeff_vand_mul, Finset.sum_mul, ← det_perm_sum_gen d, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    rw [coeff_sumpow_cast_gen d hge]
    have hkey : (((if uperm σ ≤ tg d then (tg d - uperm σ).multinomial else 0 : ℕ)) : ZMod p)
          * ∏ i : Fin h, ((d i)! : ZMod p)
        = ((Mdeg d)! : ZMod p) * ∏ i : Fin h, (((d i).descFactorial ((σ i:Fin h):ℕ)) : ZMod p) := by
      rw [← Nat.cast_prod, ← Nat.cast_mul, per_sigma_gen d hge σ, Nat.cast_mul, Nat.cast_prod]
    linear_combination ((Equiv.Perm.sign σ : ℤ) : ZMod p) * hkey
  intro hC0
  rw [hC0, zero_mul] at hident
  have hfac_ne : ((Mdeg d)! : ZMod p) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff (ZMod p) p, (inferInstance : Fact p.Prime).out.dvd_factorial]
    omega
  have hprod_ne : (∏ i : Fin h, ∏ j ∈ Ioi i, ((d j : ZMod p) - d i)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]; intro i _
    rw [Finset.prod_ne_zero_iff]; intro j hj
    rw [sub_ne_zero, Ne]; intro heq
    have : d j = d i := by
      have h1 : ((d j : ZMod p)).val = ((d i : ZMod p)).val := by rw [heq]
      rwa [ZMod.val_natCast_of_lt (hlt j), ZMod.val_natCast_of_lt (hlt i)] at h1
    have hji : i < j := Finset.mem_Ioi.mp hj
    exact absurd (hinj this) (by omega)
  exact (mul_ne_zero hfac_ne hprod_ne) hident.symm

/-- **DSH covering:** in the dense regime the k-fold restricted sumset is everything. -/
theorem dsh_cover {k : ℕ} [Fact p.Prime] (A : Finset (ZMod p)) (hk : 1 ≤ k) (hkA : k ≤ A.card)
    (hcov : p ≤ k * (A.card - k) + 1) : rsumH k A = Finset.univ := by
  have hp2 : 2 ≤ p := (inferInstance : Fact p.Prime).out.two_le
  by_contra hne
  have hAp : A.card ≤ p := by
    have := Finset.card_le_univ A; rwa [ZMod.card] at this
  have hcard_lt : (rsumH k A).card < p := by
    have h1 : rsumH k A ⊂ Finset.univ := Finset.ssubset_univ_iff.mpr hne
    have h2 := Finset.card_lt_card h1
    rwa [Finset.card_univ, ZMod.card] at h2
  set q := (p-1)/k with hqdef
  set r := (p-1)%k with hrdef
  have hrk : r < k := Nat.mod_lt _ (by omega)
  have hqr : k * q + r = p - 1 := by rw [hqdef, hrdef]; exact Nat.div_add_mod (p-1) k
  set d : Fin k → ℕ := fun i => (i:ℕ) + q + (if k - r ≤ (i:ℕ) then 1 else 0) with hddef
  have hqA : q ≤ A.card - k := by
    have h2 : k * q ≤ k * (A.card - k) :=
      le_trans (show k * q ≤ p - 1 by omega) (show p - 1 ≤ k * (A.card - k) by omega)
    exact Nat.le_of_mul_le_mul_left h2 hk
  have hge : ∀ i : Fin k, (i:ℕ) ≤ d i := fun i => by
    show (i:ℕ) ≤ (i:ℕ) + q + (if k - r ≤ (i:ℕ) then 1 else 0)
    exact le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)
  have hmono : ∀ i j : Fin k, (i:ℕ) < (j:ℕ) → d i < d j := by
    intro i j hv
    have hind : (if k - r ≤ (i:ℕ) then (1:ℕ) else 0) ≤ (if k - r ≤ (j:ℕ) then 1 else 0) := by
      by_cases hc : k - r ≤ (i:ℕ)
      · rw [if_pos hc, if_pos (show k - r ≤ (j:ℕ) by omega)]
      · rw [if_neg hc]; exact Nat.zero_le _
    show (i:ℕ) + q + (if k - r ≤ (i:ℕ) then 1 else 0) < (j:ℕ) + q + (if k - r ≤ (j:ℕ) then 1 else 0)
    exact Nat.add_lt_add_of_lt_of_le (by omega) hind
  have hinj : Function.Injective d := by
    intro i j hij
    rcases lt_trichotomy (i:ℕ) (j:ℕ) with hlt|heq|hgt
    · exact absurd (hmono i j hlt) (by rw [hij]; exact lt_irrefl _)
    · exact Fin.ext heq
    · exact absurd (hmono j i hgt) (by rw [hij]; exact lt_irrefl _)
  have hlt_A : ∀ i : Fin k, d i < A.card := by
    intro i
    have hik : (i:ℕ) < k := i.2
    show (i:ℕ) + q + (if k - r ≤ (i:ℕ) then 1 else 0) < A.card
    split_ifs with hcond
    · have hr1 : 1 ≤ r := by omega
      have hqlt : k * q < k * (A.card - k) :=
        lt_of_le_of_lt (show k * q ≤ p - 2 by omega) (show p - 2 < k * (A.card - k) by omega)
      have hq2 : q < A.card - k := Nat.lt_of_mul_lt_mul_left hqlt
      omega
    · omega
  have hlt_p : ∀ i : Fin k, d i < p := fun i => lt_of_lt_of_le (hlt_A i) hAp
  have hMd : Mdeg d = p - 1 := by
    rw [Mdeg]
    have hcount : ∑ i : Fin k, (if k - r ≤ (i:ℕ) then (1:ℕ) else 0) = r := by
      rw [Fin.sum_univ_eq_sum_range (fun i => if k - r ≤ i then (1:ℕ) else 0) k, Finset.sum_boole]
      rw [show (Finset.range k).filter (fun i => k - r ≤ i) = Finset.Ico (k - r) k by
        ext x; simp [Finset.mem_Ico, Finset.mem_range]; omega]
      simp [Nat.card_Ico]; omega
    have hsum : ∑ i : Fin k, d i = (∑ i : Fin k, (i:ℕ)) + (k * q + r) := by
      have hrw : ∀ i : Fin k, d i = ((i:ℕ) + q) + (if k - r ≤ (i:ℕ) then 1 else 0) := fun i => rfl
      simp_rw [hrw, Finset.sum_add_distrib, Finset.sum_const, Finset.card_fin, smul_eq_mul, hcount]
      ring
    rw [hsum, Nat.add_sub_cancel_left]; exact hqr
  have hMp : Mdeg d < p := by rw [hMd]; omega
  obtain ⟨H, hHsub, hHcard⟩ : ∃ H : Finset (ZMod p), rsumH k A ⊆ H ∧ H.card = p - 1 :=
    Finset.exists_superset_card_eq (by omega) (by rw [ZMod.card]; omega)
  have hcoeff : coeff (tg d) (Matrix.det (Matrix.vandermonde (fun i => (X i : MvPolynomial (Fin k) (ZMod p))))
      * ∏ c ∈ H, ((∑ i, X i) - C c)) ≠ 0 := by
    obtain ⟨low, hPeq, hlowc⟩ := prod_top (h := k) H
    rw [hPeq, mul_add, coeff_add, hHcard]
    have hlow0 : coeff (tg d) (Matrix.det (Matrix.vandermonde (fun i => (X i : MvPolynomial (Fin k) (ZMod p)))) * low) = 0 := by
      rw [coeff_vand_mul]; apply Finset.sum_eq_zero; intro σ _
      by_cases hle : uperm σ ≤ tg d
      · rw [if_pos hle, hlowc _ (le_of_eq (by rw [hHcard, tg_sub_degree_gen d hge σ hle, hMd])), mul_zero]
      · rw [if_neg hle, mul_zero]
    rw [hlow0, add_zero]
    have hcz := coeff_top_ne_zero_gen d hge hinj hlt_p hMp
    rwa [hMd] at hcz
  have hdeg_eq : (tg d).degree = (∑ i : Fin k, (i:ℕ)) + (p - 1) := by
    rw [Finsupp.degree_eq_sum]
    have : ∑ i : Fin k, (tg d) i = ∑ i : Fin k, d i := by simp only [tg_apply]
    rw [this]
    have hMd' := hMd; rw [Mdeg] at hMd'
    have hge2 : (∑ i : Fin k, (i:ℕ)) ≤ ∑ i : Fin k, d i := Finset.sum_le_sum (fun i _ => hge i)
    omega
  have htd : (Matrix.det (Matrix.vandermonde (fun i => (X i : MvPolynomial (Fin k) (ZMod p))))
      * ∏ c ∈ H, ((∑ i, X i) - C c)).totalDegree = (tg d).degree := by
    refine le_antisymm ?_ (MvPolynomial.le_totalDegree (s := tg d) (by simpa using hcoeff))
    refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
    have hv : (Matrix.det (Matrix.vandermonde (fun i => (X i : MvPolynomial (Fin k) (ZMod p))))).totalDegree
        ≤ ∑ i : Fin k, (i:ℕ) := by
      rw [vand_perm]
      refine le_trans (MvPolynomial.totalDegree_finset_sum _ _) (Finset.sup_le ?_)
      intro σ _
      refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
      have h1 : ((Equiv.Perm.sign σ : ℤ) : MvPolynomial (Fin k) (ZMod p)).totalDegree = 0 := by
        rw [← map_intCast (MvPolynomial.C (σ := Fin k) (R := ZMod p))]; exact MvPolynomial.totalDegree_C _
      have h2 : (∏ j, (X j : MvPolynomial (Fin k) (ZMod p)) ^ ((σ j : Fin k):ℕ)).totalDegree
          ≤ ∑ i : Fin k, (i:ℕ) := by
        refine le_trans (MvPolynomial.totalDegree_finset_prod _ _) ?_
        rw [← sum_perm_val σ]
        apply Finset.sum_le_sum
        intro j _
        exact le_trans (MvPolynomial.totalDegree_pow _ _) (le_of_eq (by rw [MvPolynomial.totalDegree_X, mul_one]))
      rw [h1]; omega
    have hp2' : (∏ c ∈ H, ((∑ i, X i : MvPolynomial (Fin k) (ZMod p)) - C c)).totalDegree ≤ p - 1 := by
      refine le_trans (MvPolynomial.totalDegree_finset_prod _ _) ?_
      refine le_trans (Finset.sum_le_sum (fun c _ => ?_)) (by rw [Finset.sum_const, hHcard, smul_eq_mul, mul_one])
      refine le_trans (MvPolynomial.totalDegree_sub _ _) (max_le ?_ ?_)
      · exact le_trans (MvPolynomial.totalDegree_finset_sum _ _)
          (Finset.sup_le (fun i _ => by rw [MvPolynomial.totalDegree_X]))
      · rw [MvPolynomial.totalDegree_C]; exact Nat.zero_le _
    rw [hdeg_eq]; omega
  have hSlt : ∀ i, (tg d) i < A.card := fun i => by rw [tg_apply]; exact hlt_A i
  obtain ⟨s, hsA, hnz⟩ :=
    combinatorial_nullstellensatz_exists_eval_nonzero _ (tg d) hcoeff htd (fun _ => A) hSlt
  exact hnz (dshPoly_vanish hHsub s hsA)


/-- **Alon's Theorem 1.1 (ε-form) over a prime modulus** — proven axiom-free via `dsh_cover`. -/
theorem alon_prime (k : ℕ) (hk : 2 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ p : ℕ, p.Prime → N₀ ≤ p → ∀ A : Finset (ZMod p),
      ((1 / (k : ℝ) + ε) * p < A.card) →
        ∃ B : Finset (ZMod p), B ⊆ A ∧ B.Nonempty ∧ B.card ≤ k ∧ (∑ b ∈ B, b) = 0 := by
  refine ⟨max (k ^ 2 + 1) (⌈(k : ℝ) / ε⌉₊ + 1), ?_⟩
  intro p hp hN₀ A hA
  haveI : Fact p.Prime := ⟨hp⟩
  have hkpos : (0 : ℝ) < k := by positivity
  have hppos : (0 : ℝ) < p := by
    have : 0 < p := by have := hp.pos; omega
    exact_mod_cast this
  have hpk2 : k ^ 2 + 1 ≤ p := le_trans (le_max_left _ _) hN₀
  have hpke : ⌈(k : ℝ) / ε⌉₊ + 1 ≤ p := le_trans (le_max_right _ _) hN₀
  -- p ≥ k²
  have hk2p : (k : ℝ) ^ 2 ≤ p := by
    have : (k ^ 2 : ℕ) ≤ p := by omega
    exact_mod_cast this
  -- k < ε p
  have hkeps : (k : ℝ) < ε * p := by
    have h1 : (k : ℝ) / ε ≤ ⌈(k : ℝ) / ε⌉₊ := Nat.le_ceil _
    have h2 : ((⌈(k : ℝ) / ε⌉₊ : ℕ) : ℝ) < p := by
      have : (⌈(k : ℝ) / ε⌉₊ : ℕ) + 1 ≤ p := hpke
      have := (by exact_mod_cast this : ((⌈(k : ℝ) / ε⌉₊ : ℕ) : ℝ) + 1 ≤ (p : ℝ))
      linarith
    have : (k : ℝ) / ε < p := lt_of_le_of_lt h1 h2
    rw [div_lt_iff₀ hε] at this; linarith
  -- k ≤ |A|
  have hkA : k ≤ A.card := by
    have hlt : (k : ℝ) < A.card := by
      have hkp : (k : ℝ) ≤ (1 / k) * p := by
        rw [one_div, inv_mul_eq_div, le_div_iff₀ hkpos]
        nlinarith [hk2p]
      nlinarith [hA, hε, hppos]
    have : k < A.card := by exact_mod_cast hlt
    omega
  -- p ≤ k(|A|-k)+1
  have hcov : p ≤ k * (A.card - k) + 1 := by
    have hsub : ((A.card - k : ℕ) : ℝ) = (A.card : ℝ) - k := by
      rw [Nat.cast_sub hkA]
    have hAk : (p : ℝ) + k * ε * p < k * A.card := by
      have h := mul_lt_mul_of_pos_left hA hkpos
      have hexp : k * ((1 / k + ε) * p) = p + k * ε * p := by
        field_simp
      linarith [hexp ▸ h]
    have hk2eps : (k : ℝ) ^ 2 < k * ε * p := by nlinarith [hkeps, hkpos]
    have hkey : (p : ℝ) < k * ((A.card : ℝ) - k) := by nlinarith [hAk, hk2eps]
    have : (p : ℝ) < (k * (A.card - k) : ℕ) := by rw [Nat.cast_mul, hsub]; exact hkey
    have : p < k * (A.card - k) := by exact_mod_cast this
    omega
  -- covering ⟹ 0 ∈ rsumH
  have hcover := dsh_cover A (by omega) hkA hcov
  have h0 : (0 : ZMod p) ∈ rsumH k A := by rw [hcover]; exact Finset.mem_univ _
  rw [rsumH, Finset.mem_image] at h0
  obtain ⟨s, hs, hsum⟩ := h0
  rw [Finset.mem_powersetCard] at hs
  refine ⟨s, hs.1, ?_, le_of_eq hs.2, ?_⟩
  · rw [← Finset.card_pos, hs.2]; omega
  · rw [← hsum]; rfl


/-- Uniform-over-`k` Alon (ε-form) over prime moduli — the shape the dichotomy consumes. -/
lemma alon_uniform_prime : ∀ kmax : ℕ, ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ,
    ∀ k : ℕ, 2 ≤ k → k ≤ kmax → ∀ p : ℕ, p.Prime → N₀ ≤ p →
      ∀ A : Finset (ZMod p), ((1 / (k:ℝ) + ε) * p < A.card) →
        ∃ B : Finset (ZMod p), B ⊆ A ∧ B.Nonempty ∧ B.card ≤ k ∧ (∑ b ∈ B, b) = 0 := by
  intro kmax
  induction kmax with
  | zero => intro ε _; exact ⟨0, fun k hk2 hk0 _ _ _ _ _ => absurd hk0 (by omega)⟩
  | succ m ih =>
    intro ε hε
    obtain ⟨N₁, hN₁⟩ := ih ε hε
    by_cases hm : 2 ≤ m + 1
    · obtain ⟨N₂, hN₂⟩ := alon_prime (m + 1) hm ε hε
      refine ⟨max N₁ N₂, fun k hk2 hkle p hp hN A hA => ?_⟩
      rcases Nat.lt_or_ge k (m + 1) with h | h
      · exact hN₁ k hk2 (by omega) p hp (le_trans (le_max_left _ _) hN) A hA
      · have hk : k = m + 1 := by omega
        subst hk
        exact hN₂ p hp (le_trans (le_max_right _ _) hN) A hA
    · exact ⟨N₁, fun k hk2 hkle _ _ _ _ _ => absurd hk2 (by omega)⟩

open scoped Classical

lemma sum_mem_two_q (q n : ℕ) (hq : 0 < q) (hdvd : q ∣ n) (hpos : 0 < n)
    (hlt : n < 3 * q) : n = q ∨ n = 2 * q := by
  obtain ⟨c, rfl⟩ := hdvd
  have hc3 : c < 3 := by
    have h := hlt
    rw [show 3 * q = q * 3 from Nat.mul_comm 3 q] at h
    exact Nat.lt_of_mul_lt_mul_left h
  have hc0 : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h | h
    · simp [h] at hpos
    · exact h
  interval_cases c
  · left; ring
  · right; ring

lemma sum_lt_3q {E q K : ℕ} (hE : 0 < E) (hK3 : 3 ≤ K) (hKE : K * E ≤ 3 * q)
    {B : Finset ℕ} (hB : B ⊆ Finset.Icc 1 E) (hcard : B.card ≤ K) :
    (∑ b ∈ B, b) < 3 * q := by
  have hub : ∑ b ∈ B, b ≤ B.card * E := by
    calc ∑ b ∈ B, b ≤ ∑ _b ∈ B, E :=
          Finset.sum_le_sum (fun b hb => (Finset.mem_Icc.mp (hB hb)).2)
      _ = B.card * E := by rw [Finset.sum_const, smul_eq_mul]
  have hcardE : B.card * E ≤ 3 * q := le_trans (Nat.mul_le_mul_right E hcard) hKE
  rcases lt_or_eq_of_le (le_trans hub hcardE) with h | h
  · exact h
  · exfalso
    have hse : ∑ b ∈ B, b = B.card * E := by omega
    have hallE : ∀ b ∈ B, b = E := by
      by_contra hcon
      push_neg at hcon
      obtain ⟨b0, hb0, hb0ne⟩ := hcon
      have hb0lt : b0 < E := lt_of_le_of_ne (Finset.mem_Icc.mp (hB hb0)).2 hb0ne
      have hlt : ∑ b ∈ B, b < ∑ _b ∈ B, E :=
        Finset.sum_lt_sum (fun b hb => (Finset.mem_Icc.mp (hB hb)).2) ⟨b0, hb0, hb0lt⟩
      rw [Finset.sum_const, smul_eq_mul] at hlt
      omega
    have hBsub : B ⊆ {E} := fun b hb => Finset.mem_singleton.mpr (hallE b hb)
    have hcard1 : B.card ≤ 1 := by
      have := Finset.card_le_card hBsub
      simpa using this
    have hEq : E ≤ q := by
      have h3E : 3 * E ≤ K * E := Nat.mul_le_mul_right E hK3
      omega
    have hsmall : ∑ b ∈ B, b ≤ E := by
      calc ∑ b ∈ B, b ≤ B.card * E := hub
        _ ≤ 1 * E := Nat.mul_le_mul_right E hcard1
        _ = E := one_mul E
    omega

lemma cast_injOn (E q : ℕ) (h : E ≤ q) :
    Set.InjOn (fun n : ℕ => (n : ZMod q)) (↑(Finset.Icc 1 E) : Set ℕ) := by
  intro a ha b hb hab
  simp only [Finset.coe_Icc, Set.mem_Icc] at ha hb
  rw [ZMod.natCast_eq_natCast_iff] at hab
  rcases le_total a b with hle | hle
  · have hdvd : q ∣ b - a := (Nat.modEq_iff_dvd' hle).mp hab
    have hlt : b - a < q := by omega
    have := Nat.eq_zero_of_dvd_of_lt hdvd hlt
    omega
  · have hdvd : q ∣ a - b := (Nat.modEq_iff_dvd' hle).mp hab.symm
    have hlt : a - b < q := by omega
    have := Nat.eq_zero_of_dvd_of_lt hdvd hlt
    omega

lemma exists_preimage_dvd (E q : ℕ) (hEq : E ≤ q) (hq0 : 0 < q)
    (S : Finset ℕ) (hS : S ⊆ Finset.Icc 1 E)
    (B' : Finset (ZMod q)) (hB' : B' ⊆ S.image (fun n : ℕ => (n : ZMod q)))
    (hne : B'.Nonempty) (hsum : ∑ b ∈ B', b = 0) :
    ∃ B : Finset ℕ, B ⊆ S ∧ B.Nonempty ∧ B.card = B'.card ∧ q ∣ ∑ b ∈ B, b := by
  haveI : NeZero q := ⟨by omega⟩
  have hinjS : Set.InjOn (fun n : ℕ => (n : ZMod q)) (↑S : Set ℕ) :=
    (cast_injOn E q hEq).mono (by exact_mod_cast hS)
  set B : Finset ℕ := S.filter (fun n : ℕ => (↑n : ZMod q) ∈ B') with hBdef
  have hBS : B ⊆ S := Finset.filter_subset _ _
  have hBmem : ∀ n : ℕ, n ∈ B ↔ n ∈ S ∧ (↑n : ZMod q) ∈ B' := by
    intro n; rw [hBdef]; exact Finset.mem_filter
  have hinjB : Set.InjOn (fun n : ℕ => (n : ZMod q)) (↑B : Set ℕ) :=
    hinjS.mono (by exact_mod_cast hBS)
  have hBimg : B.image (fun n : ℕ => (n : ZMod q)) = B' := by
    apply Finset.Subset.antisymm
    · intro y hy
      rw [Finset.mem_image] at hy
      obtain ⟨n, hnB, hny⟩ := hy
      rw [← hny]; exact ((hBmem n).mp hnB).2
    · intro y hy
      have hyimg : y ∈ S.image (fun n : ℕ => (n : ZMod q)) := hB' hy
      rw [Finset.mem_image] at hyimg
      obtain ⟨n, hnS, hny⟩ := hyimg
      rw [Finset.mem_image]
      exact ⟨n, (hBmem n).mpr ⟨hnS, hny ▸ hy⟩, hny⟩
  have hinjBset : ∀ x ∈ B, ∀ y ∈ B, (↑x : ZMod q) = (↑y : ZMod q) → x = y :=
    fun x hx y hy hxy => hinjB (Finset.mem_coe.mpr hx) (Finset.mem_coe.mpr hy) hxy
  refine ⟨B, hBS, ?_, ?_, ?_⟩
  · rw [← hBimg] at hne
    exact Finset.image_nonempty.mp hne
  · have hc := Finset.card_image_of_injOn hinjB
    rw [hBimg] at hc
    exact hc.symm
  · have key : ∑ b ∈ B, (b : ZMod q) = 0 := by
      rw [← hBimg] at hsum
      rwa [Finset.sum_image hinjBset] at hsum
    have hcast : ((∑ b ∈ B, b : ℕ) : ZMod q) = 0 := by
      rw [Nat.cast_sum]; exact key
    exact (CharP.cast_eq_zero_iff (ZMod q) q (∑ b ∈ B, b)).mp hcast

/-- Prime dichotomy core: `dichotomy_core` restricted to `q = τ/2` PRIME, using `alon_prime`. -/
theorem dichotomy_core_prime (ρ : ℝ) (hρ : 2 ≤ ρ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ E₀ : ℕ, ∀ E : ℕ, E₀ ≤ E → ∀ τ : ℕ, Even τ → (τ / 2).Prime → 2 * E ≤ τ → (τ : ℝ) ≤ ρ * E →
      ∀ S : Finset ℕ, S ⊆ Finset.Icc 1 E →
        (τ : ℝ) / (2 * ((3 * τ / (2 * E) : ℕ) : ℝ)) + δ * E < S.card →
        ∃ B ⊆ S, B.Nonempty ∧ (∑ b ∈ B, b) = τ := by
  have hρ0 : 0 < ρ := by linarith
  set Kmax : ℕ := (⌈(3 * ρ) / 2⌉).toNat with hKmaxdef
  obtain ⟨N₀, hAlon⟩ := alon_uniform_prime Kmax (δ / ρ) (by positivity)
  refine ⟨max (max N₀ 1) (⌈(Kmax : ℝ) * ρ / δ⌉.toNat + 1), ?_⟩
  intro E hE τ hτeven hqprime hτlow hτhigh S hSsub hScard
  have hN₀E : N₀ ≤ E := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hE
  have h1E : 1 ≤ E := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hE
  have hlossE : ⌈(Kmax : ℝ) * ρ / δ⌉.toNat + 1 ≤ E := le_trans (le_max_right _ _) hE
  have hE2pos : 0 < 2 * E := by omega
  set q : ℕ := τ / 2 with hqdef
  have hqp : q.Prime := hqprime
  have hdvd2 : 2 ∣ τ := hτeven.two_dvd
  have h2q : 2 * q = τ := by omega
  have hqE : E ≤ q := by omega
  have hq0 : 0 < q := by omega
  have hN₀q : N₀ ≤ q := le_trans hN₀E hqE
  have hE0R : (0:ℝ) < (E:ℝ) := by exact_mod_cast h1E
  have hE2R : (0:ℝ) < 2 * (E:ℝ) := by linarith
  have hτR : (2:ℝ) * (E:ℝ) ≤ (τ:ℝ) := by exact_mod_cast hτlow
  have hqR : (τ:ℝ) = 2 * (q:ℝ) := by exact_mod_cast h2q.symm
  set K : ℕ := 3 * τ / (2 * E) with hKdef
  have hK3 : 3 ≤ K := by
    rw [hKdef, Nat.le_div_iff_mul_le hE2pos]; omega
  have h2K : 2 ≤ K := by omega
  have hKE : K * E ≤ 3 * q := by
    have h1 : K * (2 * E) ≤ 3 * τ := by rw [hKdef]; exact Nat.div_mul_le_self (3 * τ) (2 * E)
    have h2 : K * (2 * E) = 2 * (K * E) := by ring
    omega
  have hxρ : (3 * (τ:ℝ)) / (2 * (E:ℝ)) ≤ 3 * ρ / 2 := by
    rw [div_le_iff₀ hE2R]; nlinarith [hτhigh]
  have hKcastle : (K:ℝ) ≤ 3 * ρ / 2 := by
    have h1 : (K:ℝ) ≤ (3 * (τ:ℝ)) / (2 * (E:ℝ)) := by
      rw [hKdef]
      calc ((3 * τ / (2 * E) : ℕ):ℝ) ≤ ((3 * τ : ℕ):ℝ) / ((2 * E : ℕ):ℝ) := Nat.cast_div_le
        _ = (3 * (τ:ℝ)) / (2 * (E:ℝ)) := by push_cast; ring
    exact le_trans h1 hxρ
  have hKle : K ≤ Kmax := by
    rw [hKmaxdef]
    have hR : (K:ℝ) ≤ (⌈3 * ρ / 2⌉ : ℝ) := le_trans hKcastle (Int.le_ceil _)
    have hKZ : (K:ℤ) ≤ ⌈3 * ρ / 2⌉ := by exact_mod_cast hR
    omega
  have hKR0 : (K:ℝ) ≠ 0 := by
    have : (3:ℝ) ≤ (K:ℝ) := by exact_mod_cast hK3
    linarith
  set Simg : Finset (ZMod q) := S.image (fun n : ℕ => (n : ZMod q)) with hSimg
  have hcardimg : Simg.card = S.card := by
    rw [hSimg]
    exact Finset.card_image_of_injOn ((cast_injOn E q hqE).mono (by exact_mod_cast hSsub))
  have hterm : (1 / (K:ℝ)) * (q:ℝ) = (τ:ℝ) / (2 * (K:ℝ)) := by
    rw [hqR]; field_simp
  have h2qρE : 2 * (q:ℝ) ≤ ρ * (E:ℝ) := by nlinarith [hτhigh, hqR]
  have hstep : (δ / ρ) * (q:ℝ) ≤ δ * (E:ℝ) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hρ0]
    nlinarith [h2qρE, hδ.le, (Nat.cast_nonneg q : (0:ℝ) ≤ (q:ℝ))]
  have hdens1 : (1 / (K : ℝ) + δ / ρ) * (q : ℝ) < (Simg.card : ℝ) := by
    rw [hcardimg]
    have expand : (1 / (K:ℝ) + δ / ρ) * (q:ℝ)
        = (1 / (K:ℝ)) * (q:ℝ) + (δ / ρ) * (q:ℝ) := by ring
    rw [expand, hterm]
    linarith [hScard, hstep]
  obtain ⟨B₁', hB₁sub, hB₁ne, hB₁cardLe, hB₁sum⟩ := hAlon K h2K hKle q hqp hN₀q Simg hdens1
  obtain ⟨B₁, hB₁subS, hB₁neN, hB₁cardEq, hB₁dvd⟩ :=
    exists_preimage_dvd E q hqE hq0 S hSsub B₁' (hSimg ▸ hB₁sub) hB₁ne hB₁sum
  have hB₁pos : 0 < ∑ b ∈ B₁, b := by
    apply Finset.sum_pos _ hB₁neN
    intro b hb
    have : 1 ≤ b := (Finset.mem_Icc.mp (hSsub (hB₁subS hb))).1
    omega
  have hB₁card : B₁.card ≤ K := by rw [hB₁cardEq]; exact hB₁cardLe
  have hB₁lt : ∑ b ∈ B₁, b < 3 * q :=
    sum_lt_3q h1E hK3 hKE (hB₁subS.trans hSsub) hB₁card
  have hB₁two := sum_mem_two_q q (∑ b ∈ B₁, b) hq0 hB₁dvd hB₁pos hB₁lt
  by_cases hcase1 : (∑ b ∈ B₁, b) = 2 * q
  · exact ⟨B₁, hB₁subS, hB₁neN, by rw [hcase1, h2q]⟩
  · have hB₁q : (∑ b ∈ B₁, b) = q := by
      rcases hB₁two with h | h
      · exact h
      · exact absurd h hcase1
    set Simg2 : Finset (ZMod q) := (S \ B₁).image (fun n : ℕ => (n : ZMod q)) with hSimg2
    have hcardimg2 : Simg2.card = (S \ B₁).card := by
      rw [hSimg2]
      exact Finset.card_image_of_injOn
        ((cast_injOn E q hqE).mono (by exact_mod_cast (Finset.sdiff_subset.trans hSsub)))
    have hsdiff : (S \ B₁).card = S.card - B₁.card := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hB₁subS]
    have hB₁leS : B₁.card ≤ S.card := Finset.card_le_card hB₁subS
    have hcardimg2R : (Simg2.card : ℝ) = (S.card : ℝ) - (B₁.card : ℝ) := by
      rw [hcardimg2, hsdiff, Nat.cast_sub hB₁leS]
    have hB₁cardR : (B₁.card : ℝ) ≤ (K:ℝ) := by exact_mod_cast hB₁card
    have hElarge : (Kmax : ℝ) * ρ / δ < (E:ℝ) := by
      have hc1 : (Kmax:ℝ) * ρ / δ ≤ (⌈(Kmax:ℝ) * ρ / δ⌉ : ℝ) := Int.le_ceil _
      have hc2 : (⌈(Kmax:ℝ) * ρ / δ⌉ : ℝ) ≤ ((⌈(Kmax:ℝ) * ρ / δ⌉.toNat : ℕ) : ℝ) := by
        exact_mod_cast Int.self_le_toNat _
      have hc3 : ((⌈(Kmax:ℝ) * ρ / δ⌉.toNat : ℕ) : ℝ) + 1 ≤ (E:ℝ) := by
        exact_mod_cast hlossE
      linarith
    have hqhalf : (δ / ρ) * (q:ℝ) ≤ δ * (E:ℝ) / 2 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hρ0]
      nlinarith [h2qρE, hδ.le,
        mul_nonneg hδ.le (show (0:ℝ) ≤ ρ * E - 2 * q by linarith [h2qρE])]
    have hKsmall : (K:ℝ) < δ * (E:ℝ) / 2 := by
      have hδE : (Kmax:ℝ) * ρ < δ * (E:ℝ) := by
        have h := (div_lt_iff₀ hδ).mp hElarge
        linarith [h, mul_comm (E:ℝ) δ]
      have hKmax0 : (0:ℝ) ≤ (Kmax:ℝ) := Nat.cast_nonneg _
      have hKKmax : (K:ℝ) ≤ (Kmax:ℝ) := by exact_mod_cast hKle
      nlinarith [hδE, hKKmax,
        mul_nonneg hKmax0 (show (0:ℝ) ≤ ρ - 2 by linarith [hρ])]
    have hdens2 : (1 / (K : ℝ) + δ / ρ) * (q : ℝ) < (Simg2.card : ℝ) := by
      rw [hcardimg2R]
      have expand : (1 / (K:ℝ) + δ / ρ) * (q:ℝ)
          = (1 / (K:ℝ)) * (q:ℝ) + (δ / ρ) * (q:ℝ) := by ring
      rw [expand, hterm]
      linarith [hScard, hqhalf, hKsmall, hB₁cardR]
    obtain ⟨B₂', hB₂sub, hB₂ne, hB₂cardLe, hB₂sum⟩ := hAlon K h2K hKle q hqp hN₀q Simg2 hdens2
    obtain ⟨B₂, hB₂subSB₁, hB₂neN, hB₂cardEq, hB₂dvd⟩ :=
      exists_preimage_dvd E q hqE hq0 (S \ B₁) (Finset.sdiff_subset.trans hSsub)
        B₂' (hSimg2 ▸ hB₂sub) hB₂ne hB₂sum
    have hB₂pos : 0 < ∑ b ∈ B₂, b := by
      apply Finset.sum_pos _ hB₂neN
      intro b hb
      have hbS : b ∈ S := Finset.sdiff_subset (hB₂subSB₁ hb)
      have : 1 ≤ b := (Finset.mem_Icc.mp (hSsub hbS)).1
      omega
    have hB₂card : B₂.card ≤ K := by rw [hB₂cardEq]; exact hB₂cardLe
    have hB₂lt : ∑ b ∈ B₂, b < 3 * q :=
      sum_lt_3q h1E hK3 hKE ((hB₂subSB₁.trans Finset.sdiff_subset).trans hSsub) hB₂card
    have hB₂two := sum_mem_two_q q (∑ b ∈ B₂, b) hq0 hB₂dvd hB₂pos hB₂lt
    by_cases hcase2 : (∑ b ∈ B₂, b) = 2 * q
    · exact ⟨B₂, hB₂subSB₁.trans Finset.sdiff_subset, hB₂neN, by rw [hcase2, h2q]⟩
    · have hB₂q : (∑ b ∈ B₂, b) = q := by
        rcases hB₂two with h | h
        · exact h
        · exact absurd h hcase2
      have hdisj : Disjoint B₁ B₂ :=
        Finset.disjoint_left.mpr
          (fun a ha hb => (Finset.mem_sdiff.mp (hB₂subSB₁ hb)).2 ha)
      refine ⟨B₁ ∪ B₂, Finset.union_subset hB₁subS (hB₂subSB₁.trans Finset.sdiff_subset),
        Finset.union_nonempty.mpr (Or.inl hB₁neN), ?_⟩
      rw [Finset.sum_union hdisj, hB₁q, hB₂q]
      omega


/-- Avoider density bound (prime subsequence), contrapositive of `dichotomy_core_prime`. -/
theorem avoider_density_bound_prime (ρ : ℝ) (hρ : 2 ≤ ρ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ E₀ : ℕ, ∀ E : ℕ, E₀ ≤ E → ∀ τ : ℕ, Even τ → (τ / 2).Prime → 2 * E ≤ τ → (τ : ℝ) ≤ ρ * E →
      ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 E → Avoids A τ →
        (A.card : ℝ) ≤ (τ : ℝ) / (2 * ((3 * τ / (2 * E) : ℕ) : ℝ)) + δ * E := by
  obtain ⟨E₀, hdich⟩ := dichotomy_core_prime ρ hρ δ hδ
  refine ⟨E₀, ?_⟩
  intro E hE τ hτeven hqp hτlow hτhigh A hAsub hAvoid
  by_contra hlt
  push_neg at hlt
  obtain ⟨B, hBsub, hBne, hBsum⟩ := hdich E hE τ hτeven hqp hτlow hτhigh A hAsub hlt
  have hBempty : B = ∅ := hAvoid B hBsub hBsum
  exact absurd hBempty (Finset.nonempty_iff_ne_empty.mp hBne)


open Filter Topology
lemma subseq_upper_of_tendsto {g : ℕ → ℝ} {β L : ℝ} (ss : ℕ → ℕ)
    (hss : Tendsto ss atTop atTop)
    (hbound : ∀ᶠ k in atTop, g (ss k) ≤ β)
    (hL : Tendsto g atTop (𝓝 L)) : L ≤ β :=
  le_of_tendsto (hL.comp hss) hbound

lemma tendsto_two_nthPrime : Tendsto (fun k => 2 * Nat.nth Nat.Prime k) atTop atTop := by
  have hsm : StrictMono (Nat.nth Nat.Prime) := Nat.nth_strictMono Nat.infinite_setOf_prime
  have h1 : Tendsto (Nat.nth Nat.Prime) atTop atTop := hsm.tendsto_atTop
  exact tendsto_atTop_mono (fun k => Nat.le_mul_of_pos_left _ (by norm_num)) h1

lemma Avoids.subset {A B : Finset ℕ} {n : ℕ} (hav : Avoids A n) (h : B ⊆ A) : Avoids B n :=
  fun C hC => hav C (hC.trans h)

lemma no_pair {A : Finset ℕ} {n x y : ℕ} (hav : Avoids A n)
    (hx : x ∈ A) (hy : y ∈ A) (hne : x ≠ y) (hsum : x + y = n) : False := by
  have hsub : ({x, y} : Finset ℕ) ⊆ A := by
    intro a ha; simp only [mem_insert, mem_singleton] at ha
    rcases ha with h | h <;> subst h <;> assumption
  have hs : ({x, y} : Finset ℕ).sum id = n := by
    rw [Finset.sum_pair hne]; simpa using hsum
  have := hav {x, y} hsub hs
  have : x ∈ (∅ : Finset ℕ) := this ▸ (by simp)
  simpa using this
def evens (M : ℕ) : Finset ℕ := (Icc 1 M).filter (fun x => Even x)

lemma evens_card (M : ℕ) : (evens M).card = M / 2 := by
  have himg : evens M = (Icc 1 (M / 2)).image (fun k => 2 * k) := by
    apply Finset.ext; intro a
    simp only [evens, mem_filter, mem_image, mem_Icc]
    constructor
    · rintro ⟨⟨ha1, ha2⟩, hev⟩
      obtain ⟨k, hk⟩ := hev
      exact ⟨k, ⟨by omega, by omega⟩, by omega⟩
    · rintro ⟨k, ⟨hk1, hk2⟩, rfl⟩
      exact ⟨⟨by omega, by omega⟩, ⟨k, by ring⟩⟩
  rw [himg, Finset.card_image_of_injective _ (by intro x y hxy; have h2 : 2 * x = 2 * y := hxy; omega), Nat.card_Icc]
  omega

lemma evens_avoids {M n : ℕ} (hodd : Odd n) : Avoids (evens M) n := by
  intro B hB hsum
  exfalso
  have hdvd : 2 ∣ B.sum id := by
    apply Finset.dvd_sum
    intro x hx
    have hx' := hB hx
    simp only [evens, mem_filter] at hx'
    obtain ⟨k, hk⟩ := hx'.2
    exact ⟨k, by simp only [id_eq]; omega⟩
  rw [hsum] at hdvd
  obtain ⟨j, hj⟩ := hodd
  omega

/-- Odd-n lower bound WITHOUT the spurious `n ≤ M`: `M/2 ≤ F M n` for odd `n`. -/
theorem oddn_lower' {M n : ℕ} (hodd : Odd n) : M / 2 ≤ F M n := by
  rw [F]
  have hmem : evens M ∈ Avoiders M n := by
    simp only [Avoiders, mem_filter, mem_powerset]
    refine ⟨?_, evens_avoids hodd⟩
    intro a ha; simp only [evens, mem_filter] at ha; exact ha.1
  calc M / 2 = (evens M).card := (evens_card M).symm
    _ ≤ (Avoiders M n).sup Finset.card := Finset.le_sup hmem

lemma high_card_le {A : Finset ℕ} {M n D : ℕ} (hn : 1 ≤ n) (hD : D = n - M)
    (hDM : D ≤ M) (hMn : M < n) (hav : Avoids A n)
    (hhi : A ⊆ Icc D M) : A.card ≤ (M - D + 2) / 2 := by
  have hmap : ∀ x ∈ A, min x (n - x) ∈ Icc D (n / 2) := by
    intro x hx
    have hx' := hhi hx; rw [mem_Icc] at hx'; obtain ⟨hx1, hx2⟩ := hx'
    rw [mem_Icc]; refine ⟨?_, ?_⟩
    · have : D ≤ n - x := by omega
      omega
    · omega
  have hinj : Set.InjOn (fun x => min x (n - x)) A := by
    intro x hx y hy hxy
    simp only at hxy
    have hxH := hhi hx; have hyH := hhi hy
    rw [mem_Icc] at hxH hyH
    by_contra hne
    have hsum : x + y = n := by omega
    exact no_pair hav hx hy hne hsum
  calc A.card ≤ (Icc D (n / 2)).card := Finset.card_le_card_of_injOn _ hmap hinj
    _ = n / 2 + 1 - D := by rw [Nat.card_Icc]
    _ ≤ (M - D + 2) / 2 := by omega
lemma split_card_bound {n M D : ℕ} {A : Finset ℕ} (hn : 1 ≤ n) (hD : D = n - M)
    (hDM : D ≤ M) (hMn : M < n) (hav : Avoids A n) (hAsub : A ⊆ Icc 1 M) :
    A.card ≤ (A ∩ Icc 1 (D - 1)).card + (M - D + 2) / 2 := by
  have hD1 : 1 ≤ D := by omega
  set Alo := A ∩ Icc 1 (D - 1) with hAlo
  set Ahi := A ∩ Icc D M with hAhi
  have hpart : A = Alo ∪ Ahi := by
    apply Finset.ext; intro a
    simp only [hAlo, hAhi, mem_union, mem_inter, mem_Icc]
    constructor
    · intro ha
      have := hAsub ha; rw [mem_Icc] at this
      rcases le_or_gt a (D - 1) with h | h
      · exact Or.inl ⟨ha, this.1, h⟩
      · exact Or.inr ⟨ha, by omega, this.2⟩
    · rintro (⟨ha, _⟩ | ⟨ha, _⟩) <;> exact ha
  have hdisj : Disjoint Alo Ahi := by
    rw [Finset.disjoint_left]; intro a ha hb
    simp only [hAlo, hAhi, mem_inter, mem_Icc] at ha hb; omega
  have hcard : A.card = Alo.card + Ahi.card := by
    rw [hpart, Finset.card_union_of_disjoint hdisj]
  have hhi : Ahi.card ≤ (M - D + 2) / 2 := by
    apply high_card_le hn hD hDM hMn (Avoids.subset hav (by
      intro a ha; simp only [hAhi, mem_inter] at ha; exact ha.1))
    intro a ha; simp only [hAhi, mem_inter] at ha; exact ha.2
  omega

lemma F_le_of_bound (M n : ℕ) (β : ℝ)
    (hβ : ∀ A : Finset ℕ, A ⊆ Icc 1 M → Avoids A n → (A.card : ℝ) ≤ β) :
    (F M n : ℝ) ≤ β := by
  have hne : (Avoiders M n).Nonempty := by
    refine ⟨∅, ?_⟩
    simp only [Avoiders, mem_filter, mem_powerset]
    exact ⟨Finset.empty_subset _, fun B hB _ => Finset.subset_empty.mp hB⟩
  obtain ⟨A, hA, hAeq⟩ := Finset.exists_mem_eq_sup (Avoiders M n) hne Finset.card
  simp only [Avoiders, mem_filter, mem_powerset] at hA
  rw [F, hAeq]
  exact hβ A hA.1 hA.2
lemma tendsto_floor_mul_div (c : ℝ) (hc : 0 ≤ c) :
    Tendsto (fun n : ℕ => (⌊c * n⌋₊ : ℝ) / n) atTop (𝓝 c) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (g := fun n : ℕ => c - 1 / n) (h := fun _ : ℕ => c)
  · have : Tendsto (fun n : ℕ => (1:ℝ) / n) atTop (𝓝 0) := tendsto_one_div_atTop_nhds_zero_nat
    have := (tendsto_const_nhds (x := c)).sub this
    simpa using this
  · exact tendsto_const_nhds
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hn0 : (0:ℝ) < n := by exact_mod_cast hn
    have hnn : 0 ≤ c * n := by positivity
    have h2 := Nat.lt_floor_add_one (c * n)
    rw [le_div_iff₀ hn0]
    have : (c - 1 / n) * n = c * n - 1 := by field_simp
    rw [this]; linarith
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hn0 : (0:ℝ) < n := by exact_mod_cast hn
    have hnn : 0 ≤ c * n := by positivity
    rw [div_le_iff₀ hn0]
    exact Nat.floor_le hnn

lemma even_upper_of_tendsto {g : ℕ → ℝ} {β L : ℝ}
    (hbound : ∀ᶠ k in atTop, g (2 * k + 2) ≤ β)
    (hL : Tendsto g atTop (𝓝 L)) : L ≤ β := by
  have hsub : Tendsto (fun k : ℕ => 2 * k + 2) atTop atTop :=
    tendsto_atTop_atTop.2 (fun b => ⟨b, fun a ha => by omega⟩)
  have hcomp : Tendsto (fun k : ℕ => g (2 * k + 2)) atTop (𝓝 L) := hL.comp hsub
  exact le_of_tendsto_of_tendsto hcomp tendsto_const_nhds hbound
theorem odd_half (c : ℝ) (hc0 : 0 < c) :
    ∀ L : ℝ, Tendsto (fun n : ℕ => (Fc c n : ℝ) / n) atTop (𝓝 L) → c / 2 ≤ L := by
  intro L hL
  set g : ℕ → ℝ := fun n => (Fc c n : ℝ) / n with hg
  have hsub : Tendsto (fun k : ℕ => 2 * k + 1) atTop atTop :=
    tendsto_atTop_atTop.2 (fun b => ⟨b, fun a ha => by omega⟩)
  have hcomp : Tendsto (fun k : ℕ => g (2 * k + 1)) atTop (𝓝 L) := hL.comp hsub
  set a : ℕ → ℝ :=
    fun k => ((⌊c * ((2 * k + 1 : ℕ) : ℝ)⌋₊ : ℝ) - 1) / (2 * ((2 * k + 1 : ℕ) : ℝ)) with ha
  have hfloorsub :
      Tendsto (fun k : ℕ => (⌊c * ((2 * k + 1 : ℕ) : ℝ)⌋₊ : ℝ) / ((2 * k + 1 : ℕ) : ℝ))
        atTop (𝓝 c) :=
    (tendsto_floor_mul_div c hc0.le).comp hsub
  have hrecip : Tendsto (fun k : ℕ => (1:ℝ) / ((2 * k + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    have h2 : Tendsto (fun k : ℕ => ((2 * k + 1 : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp hsub
    have h3 := h2.inv_tendsto_atTop
    simp only [← one_div] at h3
    exact h3
  have ha_lim : Tendsto a atTop (𝓝 (c / 2)) := by
    have hcomb : Tendsto (fun k : ℕ =>
        ((⌊c * ((2 * k + 1 : ℕ) : ℝ)⌋₊ : ℝ) / ((2 * k + 1 : ℕ) : ℝ)
          - 1 / ((2 * k + 1 : ℕ) : ℝ)) / 2) atTop (𝓝 ((c - 0) / 2)) :=
      (hfloorsub.sub hrecip).div_const 2
    have heq : ∀ k : ℕ, a k =
        ((⌊c * ((2 * k + 1 : ℕ) : ℝ)⌋₊ : ℝ) / ((2 * k + 1 : ℕ) : ℝ)
          - 1 / ((2 * k + 1 : ℕ) : ℝ)) / 2 := by
      intro k
      have hpos : (0:ℝ) < ((2 * k + 1 : ℕ) : ℝ) := by positivity
      rw [ha]; field_simp
    rw [show (c / 2 : ℝ) = (c - 0) / 2 by ring]
    exact (tendsto_congr heq).mpr hcomb
  have hbound : ∀ k : ℕ, a k ≤ g (2 * k + 1) := by
    intro k
    have hodd : Odd (2 * k + 1) := ⟨k, by ring⟩
    have hNpos : (0:ℝ) < ((2 * k + 1 : ℕ) : ℝ) := by positivity
    have hFlb : ⌊c * ((2 * k + 1 : ℕ) : ℝ)⌋₊ / 2 ≤ Fc c (2 * k + 1) := by
      rw [Fc]; exact oddn_lower' hodd
    have hFR : ((⌊c * ((2 * k + 1 : ℕ) : ℝ)⌋₊ : ℕ) : ℝ) - 1
        ≤ 2 * ((Fc c (2 * k + 1) : ℕ) : ℝ) := by
      have h1 : ((⌊c * ((2 * k + 1 : ℕ) : ℝ)⌋₊ / 2 : ℕ) : ℝ)
          ≤ ((Fc c (2 * k + 1) : ℕ) : ℝ) := by exact_mod_cast hFlb
      have h3 : (⌊c * ((2 * k + 1 : ℕ) : ℝ)⌋₊ : ℕ)
          ≤ 2 * (⌊c * ((2 * k + 1 : ℕ) : ℝ)⌋₊ / 2) + 1 := by omega
      have h3' : ((⌊c * ((2 * k + 1 : ℕ) : ℝ)⌋₊ : ℕ) : ℝ)
          ≤ 2 * ((⌊c * ((2 * k + 1 : ℕ) : ℝ)⌋₊ / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast h3
      linarith
    have hstep : ((⌊c * ((2 * k + 1 : ℕ) : ℝ)⌋₊ : ℝ) - 1) / 2 ≤ (Fc c (2 * k + 1) : ℝ) := by
      linarith [hFR]
    simp only [ha, hg]
    have hsplit : ((⌊c * ((2 * k + 1 : ℕ) : ℝ)⌋₊ : ℝ) - 1) / (2 * ((2 * k + 1 : ℕ) : ℝ))
        = (((⌊c * ((2 * k + 1 : ℕ) : ℝ)⌋₊ : ℝ) - 1) / 2) / ((2 * k + 1 : ℕ) : ℝ) := by ring
    rw [hsplit]
    gcongr
  exact le_of_tendsto_of_tendsto ha_lim hcomp (Filter.Eventually.of_forall hbound)
theorem even_half_le (c : ℝ) (hc0 : 0 < c) (hc12 : c ≤ 1 / 2) :
    ∃ β : ℝ, β < c / 2 ∧
      ∀ L : ℝ, Tendsto (fun n : ℕ => (Fc c n : ℝ) / n) atTop (𝓝 L) → L ≤ β := by
  have hcpos : (0:ℝ) < 2 * c := by linarith
  set J : ℕ := ⌊3 / (2 * c)⌋₊ with hJ
  have h3le : (3:ℝ) ≤ 3 / (2 * c) := by
    rw [le_div_iff₀ hcpos]; nlinarith [hc12, hc0]
  have hJ1 : 1 ≤ J := by
    rw [hJ]; exact Nat.le_floor (by push_cast; linarith)
  have hJR1 : (1:ℝ) ≤ (J:ℝ) := by exact_mod_cast hJ1
  have hJR0 : (0:ℝ) < (J:ℝ) := by linarith [hJR1]
  have h2Jpos : (0:ℝ) < 2 * (J:ℝ) := by linarith [hJR0]
  have hcJ : (1:ℝ) < c * J := by
    have hfl : (3:ℝ) / (2 * c) - 1 < (J:ℝ) := by rw [hJ]; exact Nat.sub_one_lt_floor _
    have hc_mul : c * (3 / (2 * c) - 1) < c * J := mul_lt_mul_of_pos_left hfl hc0
    have hlhs : c * (3 / (2 * c) - 1) = 3 / 2 - c := by field_simp
    rw [hlhs] at hc_mul; linarith [hc12, hc_mul]
  have hβlt : (1:ℝ) / (2 * J) < c / 2 := by
    rw [div_lt_iff₀ h2Jpos]; nlinarith [hcJ]
  set ε : ℝ := c / 2 - 1 / (2 * J) with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  set δ : ℝ := ε / (2 * c) with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  set β : ℝ := 1 / (2 * J) + δ * c with hβdef
  have hβc : β < c / 2 := by
    rw [hβdef, hδdef, hε]; field_simp; nlinarith [hεpos, hc0]
  refine ⟨β, hβc, ?_⟩
  intro L hL
  set ρ : ℝ := 2 / c with hρdef
  have hρ2 : 2 ≤ ρ := by rw [hρdef, le_div_iff₀ hc0]; linarith [hc12, hc0]
  obtain ⟨E₀, hADB⟩ := avoider_density_bound_prime ρ hρ2 δ hδpos
  have hev : ∀ᶠ k : ℕ in atTop, (fun n : ℕ => (Fc c n : ℝ) / n) (2 * Nat.nth Nat.Prime k) ≤ β := by
    have hbig : ∀ᶠ k : ℕ in atTop,
        E₀ ≤ ⌊c * ((2 * Nat.nth Nat.Prime k : ℕ) : ℝ)⌋₊ ∧ (⌈2 / c⌉₊ + 2 : ℕ) ≤ (2 * Nat.nth Nat.Prime k : ℕ) := by
      apply Filter.Eventually.and
      · have hnat : Tendsto (fun k : ℕ => ((2 * Nat.nth Nat.Prime k : ℕ) : ℝ)) atTop atTop :=
          tendsto_natCast_atTop_atTop.comp
            (tendsto_two_nthPrime)
        have hmul : Tendsto (fun k : ℕ => c * ((2 * Nat.nth Nat.Prime k : ℕ) : ℝ)) atTop atTop :=
          Filter.Tendsto.const_mul_atTop hc0 hnat
        have hto : Tendsto (fun k : ℕ => ⌊c * ((2 * Nat.nth Nat.Prime k : ℕ) : ℝ)⌋₊) atTop atTop :=
          tendsto_nat_floor_atTop.comp hmul
        exact hto.eventually_ge_atTop E₀
      · exact (tendsto_two_nthPrime).eventually_ge_atTop _
    filter_upwards [hbig] with k hk
    obtain ⟨hkE₀, hkbig⟩ := hk
    set n : ℕ := 2 * Nat.nth Nat.Prime k with hn
    have hnp2 : 2 ≤ Nat.nth Nat.Prime k := (Nat.prime_nth_prime k).two_le
    set E : ℕ := ⌊c * (n : ℝ)⌋₊ with hE
    have hnpos : 0 < n := by omega
    have hnR : (0:ℝ) < (n:ℝ) := by exact_mod_cast hnpos
    have hcn0 : (0:ℝ) ≤ c * n := by positivity
    have hE_le : (E : ℝ) ≤ c * n := by rw [hE]; exact Nat.floor_le hcn0
    have hEeven_ok : 2 * E ≤ n := by
      have hh : (2 * (E:ℝ)) ≤ (n:ℝ) := by nlinarith [hE_le, hc12, hnR]
      exact_mod_cast hh
    have hn2c : (2:ℝ) / c ≤ (n:ℝ) := by
      have h1 : (2:ℝ) / c ≤ (⌈2/c⌉₊ : ℝ) := Nat.le_ceil _
      have h2 : ((⌈2/c⌉₊ : ℕ):ℝ) ≤ (n:ℝ) := by exact_mod_cast (by omega : (⌈2/c⌉₊ : ℕ) ≤ n)
      linarith
    have hnc2 : (2:ℝ) ≤ (n:ℝ) * c := by
      have h := hn2c; rw [div_le_iff₀ hc0] at h; exact h
    have hcn_ge1 : (1:ℝ) ≤ c * n := by nlinarith [hnc2]
    have hEpos : 0 < E := by rw [hE]; exact Nat.floor_pos.mpr hcn_ge1
    have hτρ : (n : ℝ) ≤ ρ * E := by
      rw [hρdef, div_mul_eq_mul_div, le_div_iff₀ hc0]
      have hEfloor : (c * n : ℝ) - 1 < (E:ℝ) := by rw [hE]; exact Nat.sub_one_lt_floor _
      nlinarith [hEfloor, hnc2, hc0, hnR]
    have hEeven : Even n := ⟨Nat.nth Nat.Prime k, by rw [hn]; ring⟩
    have hnprime : (n / 2).Prime := by
      rw [hn, Nat.mul_div_cancel_left _ (by norm_num : (0:ℕ) < 2)]; exact Nat.prime_nth_prime k
    have hFb := F_le_of_bound E n
        ((n : ℝ) / (2 * ((3 * n / (2 * E) : ℕ) : ℝ)) + δ * E)
        (fun A hAsub hAv => hADB E hkE₀ n hEeven hnprime hEeven_ok hτρ A hAsub hAv)
    have hKden : J ≤ (3 * n / (2 * E) : ℕ) := by
      rw [Nat.le_div_iff_mul_le (by omega : 0 < 2 * E)]
      have hJ2c : (J:ℝ) * (2 * c) ≤ 3 := by
        have hle : (J:ℝ) ≤ 3 / (2 * c) := by rw [hJ]; exact Nat.floor_le (by positivity)
        have hx2c : (3 / (2 * c)) * (2 * c) = 3 := by field_simp
        calc (J:ℝ) * (2 * c) ≤ (3 / (2 * c)) * (2 * c) :=
              mul_le_mul_of_nonneg_right hle (by positivity)
          _ = 3 := hx2c
      have hle3 : (J : ℝ) * (2 * E) ≤ 3 * n := by
        have hp1 : (J:ℝ) * (2 * E) ≤ (J:ℝ) * (2 * (c * n)) :=
          mul_le_mul_of_nonneg_left (by linarith [hE_le]) (by positivity)
        nlinarith [hp1, hJ2c, hnR, (Nat.cast_nonneg J : (0:ℝ) ≤ (J:ℝ))]
      exact_mod_cast hle3
    have hKdenR : ((J:ℕ):ℝ) ≤ ((3 * n / (2 * E) : ℕ):ℝ) := by exact_mod_cast hKden
    show (Fc c n : ℝ) / n ≤ β
    have hFcE : Fc c n = F E n := by rw [Fc, hE]
    rw [hFcE, hβdef, div_le_iff₀ hnR]
    -- F E n ≤ (1/(2J) + δc) * n
    have h2le : 2 * (J:ℝ) ≤ 2 * ((3 * n / (2 * E) : ℕ):ℝ) := by linarith [hKdenR]
    have hrecip_le : 1 / (2 * ((3 * n / (2 * E) : ℕ):ℝ)) ≤ 1 / (2 * (J:ℝ)) :=
      one_div_le_one_div_of_le h2Jpos h2le
    have hA : (n:ℝ) / (2 * ((3 * n / (2 * E) : ℕ):ℝ)) ≤ (n:ℝ) / (2 * (J:ℝ)) := by
      rw [div_eq_mul_one_div (n:ℝ) (2 * ((3 * n / (2 * E) : ℕ):ℝ)),
          div_eq_mul_one_div (n:ℝ) (2 * (J:ℝ))]
      exact mul_le_mul_of_nonneg_left hrecip_le hnR.le
    have hB : δ * (E:ℝ) ≤ δ * c * n := by nlinarith [hE_le, hδpos.le]
    have hexp : (1 / (2 * (J:ℝ)) + δ * c) * n = (n:ℝ) / (2 * (J:ℝ)) + δ * c * n := by
      rw [add_mul]; congr 1; rw [div_mul_eq_mul_div, one_mul]
    rw [hexp]
    linarith [hFb, hA, hB]
  exact subseq_upper_of_tendsto (fun k => 2 * Nat.nth Nat.Prime k) tendsto_two_nthPrime hev hL
theorem even_half_le_high (c : ℝ) (hc12 : 1 / 2 < c) (hc1 : c < 1) :
    ∃ β : ℝ, β < c / 2 ∧
      ∀ L : ℝ, Tendsto (fun n : ℕ => (Fc c n : ℝ) / n) atTop (𝓝 L) → L ≤ β := by
  set d : ℝ := 1 - c with hd
  have hd0 : 0 < d := by rw [hd]; linarith
  have hd12 : d < 1 / 2 := by rw [hd]; linarith
  have hdpos : (0:ℝ) < 2 * d := by linarith
  set J : ℕ := ⌊3 / (2 * d)⌋₊ with hJ
  have h3le : (3:ℝ) ≤ 3 / (2 * d) := by rw [le_div_iff₀ hdpos]; nlinarith [hd12, hd0]
  have hJ1 : 1 ≤ J := by rw [hJ]; exact Nat.le_floor (by push_cast; linarith)
  have hJR1 : (1:ℝ) ≤ (J:ℝ) := by exact_mod_cast hJ1
  have hJR0 : (0:ℝ) < (J:ℝ) := by linarith [hJR1]
  have h2Jpos : (0:ℝ) < 2 * (J:ℝ) := by linarith [hJR0]
  have hdJ : (1:ℝ) < d * J := by
    have hfl : (3:ℝ) / (2 * d) - 1 < (J:ℝ) := by rw [hJ]; exact Nat.sub_one_lt_floor _
    have hc_mul : d * (3 / (2 * d) - 1) < d * J := mul_lt_mul_of_pos_left hfl hd0
    have hlhs : d * (3 / (2 * d) - 1) = 3 / 2 - d := by field_simp
    rw [hlhs] at hc_mul; linarith [hd12, hc_mul]
  have hβJlt : (1:ℝ) / (2 * J) < d / 2 := by rw [div_lt_iff₀ h2Jpos]; nlinarith [hdJ]
  -- gap and slacks
  set gap : ℝ := d / 2 - 1 / (2 * J) with hgap
  have hgap0 : 0 < gap := by rw [hgap]; linarith
  set δ : ℝ := gap / (3 * d) with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  have hδd : δ * d = gap / 3 := by rw [hδdef]; field_simp
  set η : ℝ := gap / 3 with hη
  have hη0 : 0 < η := by rw [hη]; linarith
  set β : ℝ := (c - 1 / 2) + 1 / (2 * J) + δ * d + η with hβdef
  have hβc : β < c / 2 := by
    have hβeq : β = (c - 1 / 2) + 1 / (2 * (J:ℝ)) + 2 * gap / 3 := by rw [hβdef, hδd, hη]; ring
    have hid : (c - 1 / 2) + d / 2 = c / 2 := by rw [hd]; ring
    have hlt : 1 / (2 * (J:ℝ)) + 2 * gap / 3 < d / 2 := by rw [hgap]; linarith [hβJlt]
    rw [hβeq]; linarith [hid, hlt]
  refine ⟨β, hβc, ?_⟩
  intro L hL
  set ρ : ℝ := 2 / d with hρdef
  have hρ2 : 2 ≤ ρ := by rw [hρdef, le_div_iff₀ hd0]; linarith [hd12, hd0]
  obtain ⟨E₀, hADB⟩ := avoider_density_bound_prime ρ hρ2 δ hδpos
  -- big threshold on n
  set T : ℝ := (E₀ + 3) / d + 4 / (2 * c - 1) + 2 / η + 4 with hT
  have hev : ∀ᶠ k : ℕ in atTop, (fun n : ℕ => (Fc c n : ℝ) / n) (2 * Nat.nth Nat.Prime k) ≤ β := by
    have hbig : ∀ᶠ k : ℕ in atTop, ⌈T⌉₊ ≤ (2 * Nat.nth Nat.Prime k : ℕ) :=
      (tendsto_two_nthPrime).eventually_ge_atTop _
    filter_upwards [hbig] with k hkbig
    set n : ℕ := 2 * Nat.nth Nat.Prime k with hn
    have hnp2 : 2 ≤ Nat.nth Nat.Prime k := (Nat.prime_nth_prime k).two_le
    set M : ℕ := ⌊c * (n : ℝ)⌋₊ with hM
    set D : ℕ := n - M with hDdef
    have hnpos : 0 < n := by omega
    have hnR : (0:ℝ) < (n:ℝ) := by exact_mod_cast hnpos
    have hnT : T ≤ (n:ℝ) := le_trans (Nat.le_ceil T) (by exact_mod_cast hkbig)
    have hMle : (M : ℝ) ≤ c * n := by rw [hM]; exact Nat.floor_le (by positivity)
    have hMlt2 : (c * n : ℝ) - 1 < (M:ℝ) := by rw [hM]; exact Nat.sub_one_lt_floor _
    have hpos_c : (0:ℝ) < 2 * c - 1 := by linarith
    have hnd : (n:ℝ) * d = (n:ℝ) - c * n := by rw [hd]; ring
    -- basic size facts (from n ≥ T); T's tail terms are all ≥ 0
    have hT4c : (0:ℝ) ≤ 4 / (2 * c - 1) := div_nonneg (by norm_num) hpos_c.le
    have hT2η : (0:ℝ) ≤ 2 / η := div_nonneg (by norm_num) hη0.le
    have hTE : (0:ℝ) ≤ (E₀ + 3 : ℝ) / d := div_nonneg (by positivity) hd0.le
    rw [hT] at hnT
    have hTd : (E₀ + 3 : ℝ) / d ≤ (n:ℝ) := by linarith [hnT, hT4c, hT2η]
    have hTc : (4:ℝ) / (2 * c - 1) ≤ (n:ℝ) := by linarith [hnT, hTE, hT2η]
    have hTη : (2:ℝ) / η ≤ (n:ℝ) := by linarith [hnT, hTE, hT4c]
    have hMlt : M < n := by
      have : (M:ℝ) < (n:ℝ) := by
        nlinarith [hMle, mul_pos (by linarith [hc1] : (0:ℝ) < 1 - c) hnR]
      exact_mod_cast this
    have hnDR : (n:ℝ) - (M:ℝ) = (D:ℝ) := by rw [hDdef]; push_cast [Nat.cast_sub hMlt.le]; ring
    have h4c : (4:ℝ) ≤ (n:ℝ) * (2 * c - 1) := by rw [div_le_iff₀ hpos_c] at hTc; exact hTc
    have hn2M : n ≤ 2 * M := by
      have hr : (n:ℝ) ≤ 2 * M := by nlinarith [hMlt2, h4c, hnR]
      exact_mod_cast hr
    have hDM : D ≤ M := by rw [hDdef]; omega
    have hDpos : 1 ≤ D := by rw [hDdef]; omega
    -- E₀+3 ≤ n*d ≤ D  (real), the single source for the size lower bounds
    have hnd3 : (E₀ + 3 : ℝ) ≤ (n:ℝ) * d := by have h := hTd; rwa [div_le_iff₀ hd0] at h
    have hDge : (E₀ + 3 : ℝ) ≤ (D:ℝ) := by rw [← hnDR]; nlinarith [hnd3, hnd, hMle]
    have hE : 2 ≤ D := by
      have : (2:ℝ) ≤ (D:ℝ) := by linarith [hDge]
      exact_mod_cast this
    have hDm1pos : 0 < D - 1 := by omega
    have hE₀le : E₀ ≤ D - 1 := by
      have hh : E₀ + 1 ≤ D := by
        have : (E₀ : ℝ) + 1 ≤ (D:ℝ) := by linarith [hDge]
        exact_mod_cast this
      omega
    have hDm1R : ((D - 1 : ℕ):ℝ) = (D:ℝ) - 1 := by push_cast [Nat.cast_sub hDpos]; ring
    have hEm1pos : (0:ℝ) < ((D - 1 : ℕ):ℝ) := by
      rw [hDm1R]
      have h2D : (2:ℝ) ≤ (D:ℝ) := by exact_mod_cast hE
      linarith
    have hEeven_ok : 2 * (D - 1) ≤ n := by
      have hr : (2:ℝ) * ((D - 1 : ℕ):ℝ) ≤ (n:ℝ) := by
        rw [hDm1R, ← hnDR]
        have hn2Mr : (n:ℝ) ≤ 2 * M := by exact_mod_cast hn2M
        nlinarith [hn2Mr]
      exact_mod_cast hr
    have hEeven : Even n := ⟨Nat.nth Nat.Prime k, by rw [hn]; ring⟩
    have hnprime : (n / 2).Prime := by
      rw [hn, Nat.mul_div_cancel_left _ (by norm_num : (0:ℕ) < 2)]; exact Nat.prime_nth_prime k
    have hτρ : (n : ℝ) ≤ ρ * ((D - 1 : ℕ):ℝ) := by
      rw [hρdef, div_mul_eq_mul_div, le_div_iff₀ hd0, hDm1R, ← hnDR]
      nlinarith [hnd3, hnd, hMle, (Nat.cast_nonneg E₀ : (0:ℝ) ≤ (E₀:ℝ))]
    -- per-avoider bound
    have hbnd : ∀ A : Finset ℕ, A ⊆ Icc 1 M → Avoids A n →
        (A.card : ℝ) ≤ (n : ℝ) / (2 * ((3 * n / (2 * (D - 1)) : ℕ) : ℝ))
          + δ * ((D - 1 : ℕ):ℝ) + ((M - D + 2) / 2 : ℕ) := by
      intro A hAsub hAv
      have hsplit := split_card_bound (by omega : 1 ≤ n) hDdef hDM hMlt hAv hAsub
      set Alo := A ∩ Icc 1 (D - 1) with hAlo
      have hAloSub : Alo ⊆ Icc 1 (D - 1) := by
        intro a ha; simp only [hAlo, mem_inter] at ha; exact ha.2
      have hAloAv : Avoids Alo n := Avoids.subset hAv (by
        intro a ha; simp only [hAlo, mem_inter] at ha; exact ha.1)
      have hlow := hADB (D - 1) hE₀le n hEeven hnprime hEeven_ok hτρ Alo hAloSub hAloAv
      have hcastsplit : (A.card : ℝ)
          ≤ (Alo.card : ℝ) + (((M - D + 2) / 2 : ℕ) : ℝ) := by exact_mod_cast hsplit
      have : (Alo.card : ℝ)
          ≤ (n : ℝ) / (2 * ((3 * n / (2 * (D - 1)) : ℕ) : ℝ)) + δ * ((D - 1 : ℕ):ℝ) := hlow
      linarith [hcastsplit, this]
    have hFb := F_le_of_bound M n _ hbnd
    have hFcM : Fc c n = F M n := by rw [Fc, hM]
    -- Kden' ≥ J
    have hKden : J ≤ (3 * n / (2 * (D - 1)) : ℕ) := by
      rw [Nat.le_div_iff_mul_le (by omega : 0 < 2 * (D - 1))]
      have hJ2d : (J:ℝ) * (2 * d) ≤ 3 := by
        have hle : (J:ℝ) ≤ 3 / (2 * d) := by rw [hJ]; exact Nat.floor_le (by positivity)
        have hx2d : (3 / (2 * d)) * (2 * d) = 3 := by field_simp
        calc (J:ℝ) * (2 * d) ≤ (3 / (2 * d)) * (2 * d) :=
              mul_le_mul_of_nonneg_right hle (by positivity)
          _ = 3 := hx2d
      have hDm1le : ((D - 1 : ℕ):ℝ) ≤ d * n := by
        rw [hDm1R, ← hnDR, hd]; nlinarith [hMlt2]
      have hkey : (J : ℝ) * (2 * ((D - 1 : ℕ):ℝ)) ≤ 3 * (n:ℝ) := by
        have hp1 : (J:ℝ) * (2 * ((D - 1:ℕ):ℝ)) ≤ (J:ℝ) * (2 * (d * n)) :=
          mul_le_mul_of_nonneg_left (by linarith [hDm1le]) (by positivity)
        nlinarith [hp1, hJ2d, hnR, (Nat.cast_nonneg J : (0:ℝ) ≤ (J:ℝ))]
      exact_mod_cast hkey
    have hKdenR : ((J:ℕ):ℝ) ≤ ((3 * n / (2 * (D - 1)) : ℕ):ℝ) := by exact_mod_cast hKden
    -- assemble g(n) ≤ β
    show (Fc c n : ℝ) / n ≤ β
    rw [hFcM, div_le_iff₀ hnR, hβdef]
    -- F M n ≤ β * n
    have h2le : 2 * (J:ℝ) ≤ 2 * ((3 * n / (2 * (D - 1)) : ℕ):ℝ) := by linarith [hKdenR]
    have hrecip_le : 1 / (2 * ((3 * n / (2 * (D - 1)) : ℕ):ℝ)) ≤ 1 / (2 * (J:ℝ)) :=
      one_div_le_one_div_of_le h2Jpos h2le
    have hA1 : (n:ℝ) / (2 * ((3 * n / (2 * (D - 1)) : ℕ):ℝ)) ≤ (n:ℝ) / (2 * (J:ℝ)) := by
      rw [div_eq_mul_one_div (n:ℝ), div_eq_mul_one_div (n:ℝ) (2 * (J:ℝ))]
      exact mul_le_mul_of_nonneg_left hrecip_le hnR.le
    have hDm1le2 : ((D - 1 : ℕ):ℝ) ≤ d * n := by rw [hDm1R, ← hnDR, hd]; nlinarith [hMlt2]
    have hA2 : δ * ((D - 1 : ℕ):ℝ) ≤ δ * d * n := by nlinarith [hDm1le2, hδpos.le]
    have hMval : (((M - D + 2) / 2 : ℕ) : ℝ) ≤ (c - 1 / 2) * n + η * n := by
      have hcast : (((M - D + 2) / 2 : ℕ) : ℝ) ≤ ((M - D + 2 : ℕ):ℝ) / 2 := by
        rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2)]
        have := Nat.div_mul_le_self (M - D + 2) 2; exact_mod_cast this
      have hMDcast : ((M - D + 2 : ℕ):ℝ) = 2 * (M:ℝ) - n + 2 := by
        have hMD : M - D + 2 = 2 * M - n + 2 := by omega
        rw [hMD]; push_cast [Nat.cast_sub (by omega : n ≤ 2 * M)]; ring
      rw [hMDcast] at hcast
      have hηn : (1:ℝ) ≤ η * n := by
        rw [div_le_iff₀ hη0] at hTη; nlinarith [hTη, hη0]
      have : (2 * (M:ℝ) - n + 2) / 2 ≤ (c - 1/2) * n + η * n := by
        rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)]; nlinarith [hMle, hηn]
      linarith [hcast, this]
    have hexp : ((c - 1 / 2) + 1 / (2 * (J:ℝ)) + δ * d + η) * n
        = (c - 1/2) * n + (n:ℝ) / (2 * (J:ℝ)) + δ * d * n + η * n := by
      rw [add_mul, add_mul, add_mul]; congr 2; rw [div_mul_eq_mul_div, one_mul]
    rw [hexp]
    linarith [hFb, hA1, hA2, hMval]
  exact subseq_upper_of_tendsto (fun k => 2 * Nat.nth Nat.Prime k) tendsto_two_nthPrime hev hL

/-- **Erdős #361 (irregularity, c ∈ (0,1)).** `f_c(n)/n` does not converge. -/
theorem erdos361_irregular (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) :
    ¬ ∃ L : ℝ, Tendsto (fun n : ℕ => (Fc c n : ℝ) / n) atTop (𝓝 L) := by
  rintro ⟨L, hL⟩
  have hodd : c / 2 ≤ L := odd_half c hc0 L hL
  rcases le_or_gt c (1 / 2) with hle | hgt
  · obtain ⟨β, hβc, hβ⟩ := even_half_le c hc0 hle
    have hβL := hβ L hL; linarith
  · obtain ⟨β, hβc, hβ⟩ := even_half_le_high c hgt hc1
    have hβL := hβ L hL; linarith

def extremal (M n : ℕ) : Finset ℕ := Icc ((n + 1) / 2) (n - 1) ∪ Icc (n + 1) M

/-- `n ∉ A` for any avoider (the singleton `{n}` sums to `n`). -/
lemma not_mem_of_avoids {A : Finset ℕ} {n : ℕ} (hn : 1 ≤ n) (hav : Avoids A n) : n ∉ A := by
  intro hmem
  have hsub : ({n} : Finset ℕ) ⊆ A := by simpa using hmem
  have h0 : ({n} : Finset ℕ).sum id = n := by simp
  have := hav {n} hsub h0
  simpa using this

lemma low_card_le {A : Finset ℕ} {n : ℕ} (hn : 1 ≤ n) (hav : Avoids A n)
    (hlow : A ⊆ Icc 1 (n - 1)) : A.card ≤ n / 2 := by
  have hmap : ∀ x ∈ A, min x (n - x) ∈ Icc 1 (n / 2) := by
    intro x hx
    have hx' := hlow hx
    rw [mem_Icc] at hx'
    obtain ⟨hx1, hx2⟩ := hx'
    rw [mem_Icc]
    constructor
    · -- 1 ≤ min x (n-x)
      have : 1 ≤ n - x := by omega
      omega
    · -- min x (n-x) ≤ n/2
      omega
  have hinj : Set.InjOn (fun x => min x (n - x)) A := by
    intro x hx y hy hxy
    simp only at hxy
    have hxL := hlow hx; have hyL := hlow hy
    rw [mem_Icc] at hxL hyL
    by_contra hne
    -- min x (n-x) = min y (n-y) with x ≠ y forces x + y = n
    have hsum : x + y = n := by omega
    exact no_pair hav hx hy hne hsum
  calc A.card ≤ (Icc 1 (n / 2)).card := Finset.card_le_card_of_injOn _ hmap hinj
    _ = n / 2 := by rw [Nat.card_Icc]; omega

/-- **The upper bound.** Every avoider `A ⊆ [1,M]` of `n` has `|A| ≤ M − ⌈n/2⌉`. -/
theorem avoider_card_le {A : Finset ℕ} {M n : ℕ} (hn : 1 ≤ n) (hM : n ≤ M)
    (hsub : A ⊆ Icc 1 M) (hav : Avoids A n) : A.card ≤ M - (n + 1) / 2 := by
  -- split A = (A ∩ [1,n-1]) ∪ (A ∩ [n+1,M]); n ∉ A
  set Alo := A ∩ Icc 1 (n - 1) with hAlo
  set Ahi := A ∩ Icc (n + 1) M with hAhi
  have hnotn := not_mem_of_avoids hn hav
  have hpart : A = Alo ∪ Ahi := by
    apply Finset.ext; intro a
    simp only [hAlo, hAhi, mem_union, mem_inter, mem_Icc]
    constructor
    · intro ha
      have := hsub ha; rw [mem_Icc] at this
      rcases lt_trichotomy a n with h | h | h
      · exact Or.inl ⟨ha, this.1, by omega⟩
      · exact absurd (h ▸ ha) hnotn
      · exact Or.inr ⟨ha, by omega, this.2⟩
    · rintro (⟨ha, _⟩ | ⟨ha, _⟩) <;> exact ha
  have hdisj : Disjoint Alo Ahi := by
    rw [Finset.disjoint_left]; intro a ha hb
    simp only [hAlo, hAhi, mem_inter, mem_Icc] at ha hb
    omega
  have hcard : A.card = Alo.card + Ahi.card := by
    rw [hpart, Finset.card_union_of_disjoint hdisj]
  have hlo : Alo.card ≤ n / 2 := by
    have hsubA : Alo ⊆ A := by intro a ha; simp only [hAlo, mem_inter] at ha; exact ha.1
    apply low_card_le hn (Avoids.subset hav hsubA)
    intro a ha; simp only [hAlo, mem_inter] at ha; exact ha.2
  have hhi : Ahi.card ≤ M - n := by
    calc Ahi.card ≤ (Icc (n + 1) M).card := by
            apply Finset.card_le_card; intro a ha
            simp only [hAhi, mem_inter] at ha; exact ha.2
      _ = M - n := by rw [Nat.card_Icc]; omega
  omega

/-! ### Lower bound: the extremal construction -/

lemma extremal_subset {M n : ℕ} (hn : 1 ≤ n) (hM : n ≤ M) : extremal M n ⊆ Icc 1 M := by
  intro a ha
  simp only [extremal, mem_union, mem_Icc] at ha
  rw [mem_Icc]
  rcases ha with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega

lemma extremal_avoids {M n : ℕ} (hn : 1 ≤ n) (hM : n ≤ M) : Avoids (extremal M n) n := by
  intro B hB hsum
  by_contra hBne
  replace hBne : B.Nonempty := Finset.nonempty_iff_ne_empty.mpr hBne
  -- every element of B is ≥ ⌈n/2⌉; if two or more, sum > n; if one, < n unless it is ... but all < n or > n
  have hmem : ∀ b ∈ B, (n + 1) / 2 ≤ b := by
    intro b hb
    have := hB hb
    simp only [extremal, mem_union, mem_Icc] at this
    rcases this with ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
  have hne_n : ∀ b ∈ B, b ≠ n := by
    intro b hb hbn
    have := hB hb
    simp only [extremal, mem_union, mem_Icc] at this
    omega
  obtain ⟨b0, hb0⟩ := hBne
  rcases eq_or_lt_of_le (Finset.one_le_card.mpr ⟨b0, hb0⟩) with h1 | h2
  · -- |B| = 1: B = {b0}, sum = b0, but b0 ≠ n and b0 ... sum = n means b0 = n, contra
    have : B = {b0} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      refine ⟨hb0, ?_⟩; intro x hx
      have := Finset.card_le_one.mp (le_of_eq h1.symm) x hx b0 hb0
      exact this
    rw [this] at hsum; simp at hsum
    exact hne_n b0 hb0 hsum
  · -- |B| ≥ 2: pick two distinct, both ≥ (n+1)/2, sum ≥ n+1 > n but total sum = n
    obtain ⟨b1, hb1, b2, hb2, hb12⟩ := Finset.one_lt_card.mp h2
    have hb1v := hmem b1 hb1
    have hb2v := hmem b2 hb2
    have hpair : ({b1, b2} : Finset ℕ) ⊆ B := by
      intro a ha; simp only [mem_insert, mem_singleton] at ha
      rcases ha with h | h <;> subst h <;> assumption
    have hle : b1 + b2 ≤ ∑ x ∈ B, x := by
      have h : ∑ x ∈ ({b1, b2} : Finset ℕ), x ≤ ∑ x ∈ B, x :=
        Finset.sum_le_sum_of_subset hpair
      rwa [Finset.sum_pair hb12] at h
    have hsum' : (∑ x ∈ B, x) = n := hsum
    -- b1,b2 ≥ ⌈n/2⌉ and distinct ⟹ b1+b2 > n (odd) or = n only if equal (even, excluded)
    omega

lemma extremal_card {M n : ℕ} (hn : 1 ≤ n) (hM : n ≤ M) :
    (extremal M n).card = M - (n + 1) / 2 := by
  have hdisj : Disjoint (Icc ((n + 1) / 2) (n - 1)) (Icc (n + 1) M) := by
    rw [Finset.disjoint_left]; intro a ha hb
    rw [mem_Icc] at ha hb; omega
  rw [extremal, Finset.card_union_of_disjoint hdisj, Nat.card_Icc, Nat.card_Icc]
  omega

/-! ### Assemble F -/

theorem erdos361_cge1 (M n : ℕ) (hn : 1 ≤ n) (hM : n ≤ M) :
    F M n = M - (n + 1) / 2 := by
  apply le_antisymm
  · -- F ≤ M - ⌈n/2⌉: every avoider bounded
    rw [F, Finset.sup_le_iff]
    intro A hA
    simp only [Avoiders, mem_filter, mem_powerset] at hA
    exact avoider_card_le hn hM hA.1 hA.2
  · -- F ≥ M - ⌈n/2⌉: extremal achieves it
    rw [F]
    have hmem : extremal M n ∈ Avoiders M n := by
      simp only [Avoiders, mem_filter, mem_powerset]
      exact ⟨extremal_subset hn hM, extremal_avoids hn hM⟩
    calc M - (n + 1) / 2 = (extremal M n).card := (extremal_card hn hM).symm
      _ ≤ (Avoiders M n).sup Finset.card := Finset.le_sup hmem



end Erdos361
