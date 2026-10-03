/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Erdos1054.Spine
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Data.Nat.Squarefree
import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.Harmonic.Bounds

set_option autoImplicit false

/-!
# EP1054 `prop:sv-second-moment`, the small-`h` case: the `SvSmallH` package of the spine

Discharges eight obligations of `Principia.Erdos1054.Spine` for EP1054.tex lines 1531–1860
(`Campaigns/Erdos-1054/collab-paper/EP1054.tex`).

Leaves (from the definitions and Mathlib alone):
* `leaf_Claim_SvResiduePairCount` (lines 1756–1762) — for squarefree `h` with `k`, `σ(k)` units
  mod `h`, the residue pairs number at most `τ(h)`. Over each prime `ℓ ∣ h` the pair is a root pair
  of `X² − (a+b)X + ab`, so `a ≡ a₀` or `a ≡ b₀`; the map `(a, b) ↦ gcd(h, |a − a₀|)` into the
  divisors of `h` is injective (squarefree CRT, `sqf_dvd_of_primes`).
* `leaf_Claim_SvSmallHSquarefree` (lines 1740–1747) — `q₀² ∣ h` forces `q₀ > y(n)` (roughness of
  `s(n)/d`), then `q₀ > n^{10/27}` (square exclusion), and `q₀² > n^{20/27} > X^{17/54} > X^{10/33}`.

Links:
* `link_Claim_SvSmallHResidues` (lines 1749–1758) — a prime of `h` dividing `n` or `σ(n)` divides
  `gcd(n, σ(n)) = d`, and then `dℓ` is a `Y`-smooth divisor of `s(n)` exceeding `D_Y(s(n)) = d`.
* `link_Eq_SvIntermediateTotient` (lines 1763–1778) — `∏ p/(p−1) ≤ exp ∑ 1/(p−1)`; the case
  `𝔣 ≤ 1` gives `e²`, the case `𝔣 > 1` Mertens on `((log log X)², log X]` (`mertens_interval`).
* `link_Eq_SvFSum` (lines 1780–1815) — Brun–Titchmarsh over `⌈log X⌉` dyadic blocks
  (`BT_dyadic`, `class_recip`); the admissible `q` for fixed `r, q₀` lie in one class mod `q₀h`;
  `φ(q₀h) = (q₀−1)φ(h)`, `1/φ(h) ≤ ζ(2)B/h`; `∑_{q₀ > (log log X)²} q₀⁻² ≤ 2/(log log X)²`; the
  sparse `r`-count for `h > X^{1/20}` (`ap_recip_le`).
* `link_Eq_SvQRSum` (lines 1816–1827) — the same progression bounds without `𝔣`, plus `eq:sv-f-sum`.
* `link_Claim_SvSmallH` (lines 1733–1859) — the regrouping of the collision pairs into
  `(n', h, k, q, r)` (`pair_regroup`), at most `τ(h)` residue pairs, `eq:sv-qr-sum`, the `k`-sum
  (`eq:sv-k-reciprocal`), the `h`-sum (`∑ τ(h)/h ≤ (σ(m)/m)²`, `∑ τ(h) ≤ τ(m)²` with the divisor
  bound at `ε = 1/200`), and the `n'`-sum (`eq:sv-m-reciprocal`).
* `link_Prop_SvSecondMoment` (lines 1531–1860) — `∑_u R_d(u)² = #{(M, M') : s(M) = s(M')}`; the
  diagonal is `#𝒜_d(X)`; off-diagonal pairs inject into the realised prime pairs of collision pairs,
  bounded by the sieve, `eq:sv-totient` and the `A_3` reduction, then `eq:sv-reduced-collision-sum`.

`eq:sv-collision` (`s(pn) = p s(n) + σ(n)` for a prime `p ∤ n`) is re-proved here
(`SvSmallH.collision_identity`) and used where the paper uses `dh ∣ σ(n) − σ(n')`.
-/

namespace Principia.Erdos1054.Proofs.SvSmallH

open Finset

/-- Over a prime, a pair with prescribed sum and product is a root pair: `a ≡ a₀` or `a ≡ b₀`. -/
lemma prime_dvd_sub_or {p : ℕ} (hp : p.Prime) {a b a₀ b₀ : ℤ}
    (hs : (p : ℤ) ∣ (a + b) - (a₀ + b₀)) (hm : (p : ℤ) ∣ a * b - a₀ * b₀) :
    (p : ℤ) ∣ a - a₀ ∨ (p : ℤ) ∣ a - b₀ := by
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  apply hpz.dvd_or_dvd
  have e : (a - a₀) * (a - b₀) = a * ((a + b) - (a₀ + b₀)) - (a * b - a₀ * b₀) := by ring
  rw [e]
  exact dvd_sub (dvd_mul_of_dvd_right hs _) hm

/-- A squarefree `h` divides `x` once every prime factor of `h` does. -/
lemma sqf_dvd_of_primes {h : ℕ} (hsq : Squarefree h) {x : ℤ}
    (hx : ∀ p : ℕ, p.Prime → p ∣ h → (p : ℤ) ∣ x) : (h : ℤ) ∣ x := by
  rw [Int.natCast_dvd]
  rw [← Nat.prod_primeFactors_of_squarefree hsq]
  apply Finset.prod_primes_dvd
  · intro a ha
    exact (Nat.prime_of_mem_primeFactors ha).prime
  · intro a ha
    have hap := Nat.prime_of_mem_primeFactors ha
    have := hx a hap (Nat.dvd_of_mem_primeFactors ha)
    exact Int.natCast_dvd.mp this

/-- Two naturals below `h` congruent modulo `h` are equal. -/
lemma eq_of_lt_of_dvd {h a a' : ℕ} (ha : a < h) (ha' : a' < h) (hd : (h : ℤ) ∣ (a : ℤ) - a') :
    a = a' := by
  have h0 : ((a : ℤ) - a') = 0 := by
    apply Int.eq_zero_of_abs_lt_dvd hd
    rw [abs_lt]
    constructor <;> omega
  omega

/-- The two congruences of a residue pair give the sum and product modulo `h`. -/
lemma residuePair_sum_prod {h n' k a b a₀ b₀ : ℕ} (hk : Nat.Coprime k h)
    (hsk : Nat.Coprime (sig k) h) (H : SV.ResiduePair h n' k a b)
    (H₀ : SV.ResiduePair h n' k a₀ b₀) :
    (h : ℤ) ∣ ((a : ℤ) + b) - ((a₀ : ℤ) + b₀) ∧ (h : ℤ) ∣ (a : ℤ) * b - (a₀ : ℤ) * b₀ := by
  obtain ⟨H1, H2⟩ := H
  obtain ⟨H01, H02⟩ := H₀
  have d1 := (Nat.modEq_iff_dvd.mp H1)
  have d01 := (Nat.modEq_iff_dvd.mp H01)
  have d2 := (Nat.modEq_iff_dvd.mp H2)
  have d02 := (Nat.modEq_iff_dvd.mp H02)
  push_cast at d1 d01 d2 d02
  have hkc : IsCoprime (h : ℤ) (k : ℤ) := Nat.isCoprime_iff_coprime.mpr hk.symm
  have hskc : IsCoprime (h : ℤ) (sig k : ℤ) := Nat.isCoprime_iff_coprime.mpr hsk.symm
  have hprod : (h : ℤ) ∣ (a : ℤ) * b - (a₀ : ℤ) * b₀ := by
    have : (h : ℤ) ∣ ((a : ℤ) * b - (a₀ : ℤ) * b₀) * k := by
      have e : ((a : ℤ) * b - (a₀ : ℤ) * b₀) * k =
          ((n' : ℤ) - a₀ * b₀ * k) - ((n' : ℤ) - a * b * k) := by ring
      rw [e]
      exact dvd_sub d01 d1
    exact hkc.dvd_of_dvd_mul_right this
  refine ⟨?_, hprod⟩
  have h3 : (h : ℤ) ∣ ((a : ℤ) * b + a + b - ((a₀ : ℤ) * b₀ + a₀ + b₀)) * (sig k : ℤ) := by
    have e : ((a : ℤ) * b + a + b - ((a₀ : ℤ) * b₀ + a₀ + b₀)) * (sig k : ℤ) =
        ((n' : ℤ) - (a₀ + 1) * (b₀ + 1) * (sig k : ℤ)) -
          ((n' : ℤ) - (a + 1) * (b + 1) * (sig k : ℤ)) := by ring
    rw [e]
    exact dvd_sub d02 d2
  have h4 := hskc.dvd_of_dvd_mul_right h3
  have e : ((a : ℤ) + b) - ((a₀ : ℤ) + b₀) =
      ((a : ℤ) * b + a + b - ((a₀ : ℤ) * b₀ + a₀ + b₀)) - ((a : ℤ) * b - (a₀ : ℤ) * b₀) := by ring
  rw [e]
  exact dvd_sub h4 hprod

end Principia.Erdos1054.Proofs.SvSmallH

namespace Principia.Erdos1054.Proofs

open Finset

theorem leaf_Claim_SvResiduePairCount : Principia.Erdos1054.Claim_SvResiduePairCount := by
  intro h n' k hsq hk hsk
  classical
  set S := (Finset.range h ×ˢ Finset.range h).filter
    (fun ab : ℕ × ℕ => SV.ResiduePair h n' k ab.1 ab.2) with hS
  rcases S.eq_empty_or_nonempty with hE | ⟨x₀, hx₀⟩
  · rw [hE]
    simp
  have hmem : ∀ x ∈ S, x.1 < h ∧ x.2 < h ∧ SV.ResiduePair h n' k x.1 x.2 := by
    intro x hx
    rw [hS, Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range] at hx
    exact ⟨hx.1.1, hx.1.2, hx.2⟩
  have hh0 : h ≠ 0 := by
    rintro rfl
    exact not_squarefree_zero hsq
  obtain ⟨_, _, H₀⟩ := hmem x₀ hx₀
  let φ : ℕ × ℕ → ℕ := fun x => Nat.gcd h (Int.natAbs ((x.1 : ℤ) - x₀.1))
  refine Finset.card_le_card_of_injOn φ ?_ ?_
  · intro x _
    rw [Finset.mem_coe, Nat.mem_divisors]
    exact ⟨Nat.gcd_dvd_left _ _, hh0⟩
  · intro x hx y hy hxy
    rw [Finset.mem_coe] at hx hy
    obtain ⟨hx1, hx2, Hx⟩ := hmem x hx
    obtain ⟨hy1, hy2, Hy⟩ := hmem y hy
    obtain ⟨sx, px⟩ := SvSmallH.residuePair_sum_prod hk hsk Hx H₀
    obtain ⟨sy, py⟩ := SvSmallH.residuePair_sum_prod hk hsk Hy H₀
    have key : ∀ p : ℕ, p.Prime → p ∣ h → (p : ℤ) ∣ (x.1 : ℤ) - y.1 := by
      intro p hp hph
      have hpx : (p : ℤ) ∣ (x.1 : ℤ) - x₀.1 ∨ (p : ℤ) ∣ (x.1 : ℤ) - x₀.2 :=
        SvSmallH.prime_dvd_sub_or hp (dvd_trans (Int.natCast_dvd_natCast.mpr hph) sx)
          (dvd_trans (Int.natCast_dvd_natCast.mpr hph) px)
      have hpy : (p : ℤ) ∣ (y.1 : ℤ) - x₀.1 ∨ (p : ℤ) ∣ (y.1 : ℤ) - x₀.2 :=
        SvSmallH.prime_dvd_sub_or hp (dvd_trans (Int.natCast_dvd_natCast.mpr hph) sy)
          (dvd_trans (Int.natCast_dvd_natCast.mpr hph) py)
      -- `p ∣ x.1 - x₀.1 ↔ p ∣ y.1 - x₀.1`, through the equal gcds
      have hiff : (p : ℤ) ∣ (x.1 : ℤ) - x₀.1 ↔ (p : ℤ) ∣ (y.1 : ℤ) - x₀.1 := by
        have hxy' : Nat.gcd h (Int.natAbs ((x.1 : ℤ) - x₀.1)) =
            Nat.gcd h (Int.natAbs ((y.1 : ℤ) - x₀.1)) := hxy
        constructor
        · intro hd
          have h1 : p ∣ Nat.gcd h (Int.natAbs ((x.1 : ℤ) - x₀.1)) :=
            Nat.dvd_gcd hph (Int.natCast_dvd.mp hd)
          rw [hxy'] at h1
          exact Int.natCast_dvd.mpr (dvd_trans h1 (Nat.gcd_dvd_right _ _))
        · intro hd
          have h1 : p ∣ Nat.gcd h (Int.natAbs ((y.1 : ℤ) - x₀.1)) :=
            Nat.dvd_gcd hph (Int.natCast_dvd.mp hd)
          rw [← hxy'] at h1
          exact Int.natCast_dvd.mpr (dvd_trans h1 (Nat.gcd_dvd_right _ _))
      by_cases hc : (p : ℤ) ∣ (x.1 : ℤ) - x₀.1
      · have hc' := hiff.mp hc
        have e : (x.1 : ℤ) - y.1 = ((x.1 : ℤ) - x₀.1) - ((y.1 : ℤ) - x₀.1) := by ring
        rw [e]
        exact dvd_sub hc hc'
      · have hc' : ¬ (p : ℤ) ∣ (y.1 : ℤ) - x₀.1 := fun h' => hc (hiff.mpr h')
        have ha := hpx.resolve_left hc
        have hb := hpy.resolve_left hc'
        have e : (x.1 : ℤ) - y.1 = ((x.1 : ℤ) - x₀.2) - ((y.1 : ℤ) - x₀.2) := by ring
        rw [e]
        exact dvd_sub ha hb
    have h1 : x.1 = y.1 :=
      SvSmallH.eq_of_lt_of_dvd hx1 hy1 (SvSmallH.sqf_dvd_of_primes hsq key)
    have h2 : x.2 = y.2 := by
      apply SvSmallH.eq_of_lt_of_dvd hx2 hy2
      have e : (x.2 : ℤ) - y.2 = (((x.1 : ℤ) + x.2) - ((x₀.1 : ℤ) + x₀.2)) -
          (((y.1 : ℤ) + y.2) - ((x₀.1 : ℤ) + x₀.2)) - ((x.1 : ℤ) - y.1) := by ring
      have h0 : (x.1 : ℤ) - y.1 = 0 := by rw [h1, sub_self]
      rw [e, h0, sub_zero]
      exact dvd_sub sx sy
    exact Prod.ext h1 h2

end Principia.Erdos1054.Proofs

namespace Principia.Erdos1054.Proofs.SvSmallH

open Finset

/-! ## Arithmetic of the tuples of `𝒜₀(X)` -/

lemma rpow_lt_of_lt {X a b : ℝ} (hX : 1 < X) (hab : a < b) : X ^ a < X ^ b :=
  (Real.rpow_lt_rpow_left_iff hX).mpr hab

/-- The size relations of a tuple of `eq:sv-factorization` once `X ≥ 2^15`. -/
lemma tuple_facts {D : ℕ} {X : ℝ} (hX : (2 : ℝ) ^ 15 ≤ X) {p q r k : ℕ}
    (ht : S4a.A0Tuple D X p q r k) :
    p.Prime ∧ q.Prime ∧ r.Prime ∧ 1 ≤ k ∧ k < r ∧ r * k < q ∧ q * r * k < p ∧
      X ^ ((17 : ℝ) / 40) < ((q * r * k : ℕ) : ℝ) ∧
      ((q * r * k : ℕ) : ℝ) ≤ X ^ ((7 : ℝ) / 15) ∧ ((p * q * r * k : ℕ) : ℝ) ≤ X := by
  obtain ⟨hp, hq, hr, _, hk1, hk2, hr1, hr2, hq1, hq2, hp1, hp2⟩ := ht
  have hX1 : (1 : ℝ) < X := by linarith [show (1 : ℝ) < 2 ^ 15 by norm_num]
  have hX0 : (0 : ℝ) < X := by linarith
  have hk0 : (0 : ℝ) < k := lt_of_le_of_lt (Real.rpow_nonneg hX0.le _) hk1
  have hkr : (k : ℝ) < r := by
    calc (k : ℝ) ≤ X ^ ((1 : ℝ) / 60) := hk2
      _ < X ^ ((1 : ℝ) / 15) := rpow_lt_of_lt hX1 (by norm_num)
      _ < r := hr1
  have hr0 : (0 : ℝ) < r := by linarith
  have hrk : (r : ℝ) * k < q := by
    calc (r : ℝ) * k ≤ X ^ ((1 : ℝ) / 12) * X ^ ((1 : ℝ) / 60) :=
          mul_le_mul hr2 hk2 hk0.le (Real.rpow_nonneg hX0.le _)
      _ = X ^ ((1 : ℝ) / 12 + 1 / 60) := (Real.rpow_add hX0 _ _).symm
      _ < X ^ ((7 : ℝ) / 20) := rpow_lt_of_lt hX1 (by norm_num)
      _ < q := hq1
  have hq0 : (0 : ℝ) < q := lt_of_le_of_lt (by positivity) hrk
  have hn_lo : X ^ ((17 : ℝ) / 40) < (q : ℝ) * r * k := by
    have e : X ^ ((17 : ℝ) / 40) = X ^ ((7 : ℝ) / 20) * X ^ ((1 : ℝ) / 15) * X ^ ((1 : ℝ) / 120) := by
      rw [← Real.rpow_add hX0, ← Real.rpow_add hX0]
      norm_num
    rw [e]
    have h1 : X ^ ((7 : ℝ) / 20) * X ^ ((1 : ℝ) / 15) < q * r :=
      mul_lt_mul'' hq1 hr1 (Real.rpow_nonneg hX0.le _) (Real.rpow_nonneg hX0.le _)
    exact mul_lt_mul'' h1 hk1 (by positivity) (Real.rpow_nonneg hX0.le _)
  have hn_hi : (q : ℝ) * r * k ≤ X ^ ((7 : ℝ) / 15) := by
    have e : X ^ ((7 : ℝ) / 15) = X ^ ((11 : ℝ) / 30) * X ^ ((1 : ℝ) / 12) * X ^ ((1 : ℝ) / 60) := by
      rw [← Real.rpow_add hX0, ← Real.rpow_add hX0]
      norm_num
    rw [e]
    exact mul_le_mul (mul_le_mul hq2 hr2 hr0.le (Real.rpow_nonneg hX0.le _)) hk2 hk0.le
      (by positivity)
  have hn0 : (0 : ℝ) < q * r * k := by positivity
  have h2 : (2 : ℝ) ≤ X ^ ((1 : ℝ) / 15) := by
    have e : ((2 : ℝ) ^ 15) ^ ((1 : ℝ) / 15) = 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      norm_num
    calc (2 : ℝ) = ((2 : ℝ) ^ 15) ^ ((1 : ℝ) / 15) := e.symm
      _ ≤ X ^ ((1 : ℝ) / 15) := Real.rpow_le_rpow (by norm_num) hX (by norm_num)
  have hsq : 2 * ((q : ℝ) * r * k) * ((q : ℝ) * r * k) ≤ X := by
    calc 2 * ((q : ℝ) * r * k) * ((q : ℝ) * r * k)
        ≤ X ^ ((1 : ℝ) / 15) * X ^ ((7 : ℝ) / 15) * X ^ ((7 : ℝ) / 15) := by
          apply mul_le_mul (mul_le_mul h2 hn_hi hn0.le (Real.rpow_nonneg hX0.le _)) hn_hi hn0.le
          positivity
      _ = X := by
          rw [← Real.rpow_add hX0, ← Real.rpow_add hX0]
          norm_num
  have hnp : (q : ℝ) * r * k < p := by
    have h3 : (q : ℝ) * r * k ≤ X / (2 * (q : ℝ) * r * k) := by
      rw [le_div_iff₀ (by positivity)]
      calc (q : ℝ) * r * k * (2 * (q : ℝ) * r * k) = 2 * ((q : ℝ) * r * k) * ((q : ℝ) * r * k) := by
            ring
        _ ≤ X := hsq
    linarith
  have hM : (p : ℝ) * (q * r * k) ≤ X := by
    have := (le_div_iff₀ hn0).mp (by simpa [mul_assoc] using hp2)
    linarith
  refine ⟨hp, hq, hr, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact_mod_cast hk0
  · exact_mod_cast hkr
  · exact_mod_cast hrk
  · exact_mod_cast hnp
  · push_cast
    exact hn_lo
  · push_cast
    exact hn_hi
  · push_cast
    calc (p : ℝ) * q * r * k = (p : ℝ) * (q * r * k) := by ring
      _ ≤ X := hM

/-! ## Unpacking a regular family -/

/-- The properties of `lem:sv-regular` at the levels of one member tuple of the class `d`. -/
lemma member_regular {D : ℕ} {B X : ℝ} {A : Finset ℕ}
    (hreg : ∀ M ∈ A, SV.RegularMember D B X M) {d p q r k : ℕ}
    (hm : SV.MemberTuple D A X d p q r k) :
    SV.RegularAt (SV.Ycut X) d k ∧ SV.RegularAt (SV.Ycut X) d (r * k) ∧
      SV.RegularAt (SV.Ycut X) d (q * r * k) ∧ SV.RegularAt (SV.Ycut X) d (p * q * r * k) ∧
      SV.SqExcl (q * r * k) ∧ Eq_SvLP25 X (q * r * k) ∧ Eq_SvImageAbundancy B (q * r * k) := by
  obtain ⟨ht, hA, hsd⟩ := hm
  have h := hreg _ hA p q r k ht rfl
  rw [hsd] at h
  exact h

/-- `n ≤ σ(n)` for `n ≥ 1`. -/
lemma le_sig {n : ℕ} (hn : n ≠ 0) : n ≤ sig n := by
  show n ≤ ArithmeticFunction.sigma 1 n
  rw [ArithmeticFunction.sigma_one_apply]
  exact Finset.single_le_sum (fun i _ => Nat.zero_le i) (Nat.mem_divisors_self n hn)

lemma sig_eq_aliquot_add {n : ℕ} (hn : n ≠ 0) : sig n = aliquot n + n := by
  have := le_sig hn
  unfold aliquot
  omega

/-- `σ(p) = p + 1` for a prime `p`. -/
lemma sig_prime {p : ℕ} (hp : p.Prime) : sig p = p + 1 := by
  show ArithmeticFunction.sigma 1 p = p + 1
  rw [ArithmeticFunction.sigma_one_apply, Nat.Prime.divisors hp, Finset.sum_pair hp.one_lt.ne]
  omega

/-- `σ(mn) = σ(m)σ(n)` for coprime `m, n`. -/
lemma sig_mul {m n : ℕ} (h : Nat.Coprime m n) : sig (m * n) = sig m * sig n :=
  ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime h

/-- The consequences of `(i)` of `lem:sv-regular` used below. -/
lemma regAt_basic {Y : ℝ} {d t : ℕ} (ht : 1 ≤ t) (H : SV.RegularAt Y d t) :
    1 ≤ d ∧ d ∣ t ∧ d ∣ sig t ∧ d ∣ aliquot t ∧ aliquot t ≠ 0 ∧ IsSmooth Y d ∧
      (∀ e : ℕ, e ∣ aliquot t → IsSmooth Y e → e ≤ d) ∧ IsRough (yLP t) (aliquot t / d) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := H
  have hd1 : 1 ≤ d := by
    rw [h1]
    exact Nat.gcd_pos_of_pos_left _ ht
  have hdt : d ∣ t := h1 ▸ Nat.gcd_dvd_left _ _
  have hds : d ∣ sig t := h1 ▸ Nat.gcd_dvd_right _ _
  have hda : d ∣ aliquot t := Nat.dvd_sub hds hdt
  classical
  -- `d` is the maximum of the `Y`-smooth divisors of `s(t)`
  have hsp : d = ((aliquot t).divisors.filter (fun e => IsSmooth Y e)).sup id := by
    rw [h3]
    unfold SV.smoothPart
    congr 1
  have hne : ((aliquot t).divisors.filter (fun e => IsSmooth Y e)).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hE
    rw [hE, Finset.sup_empty] at hsp
    simp at hsp
    omega
  obtain ⟨i, hi, hieq⟩ := Finset.exists_mem_eq_sup _ hne id
  rw [Finset.mem_filter, Nat.mem_divisors] at hi
  have hdi : d = i := by rw [hsp, hieq]; rfl
  refine ⟨hd1, hdt, hds, hda, hi.1.2, hdi ▸ hi.2, ?_, h5⟩
  intro e he hse
  by_cases h0 : aliquot t = 0
  · exact absurd h0 hi.1.2
  have hmem : e ∈ (aliquot t).divisors.filter (fun e => IsSmooth Y e) := by
    rw [Finset.mem_filter, Nat.mem_divisors]
    exact ⟨⟨he, h0⟩, hse⟩
  rw [hsp]
  exact Finset.le_sup (f := id) hmem

/-- `d ℓ` is `Y`-smooth when `ℓ` is a prime factor of the `Y`-smooth `d`. -/
lemma isSmooth_mul_of_dvd {Y : ℝ} {d ℓ : ℕ} (hd : d ≠ 0) (hℓ : ℓ.Prime) (hℓd : ℓ ∣ d)
    (hs : IsSmooth Y d) : IsSmooth Y (d * ℓ) := by
  intro x hx
  rw [Nat.primeFactors_mul hd hℓ.ne_zero, Finset.mem_union] at hx
  rcases hx with hx | hx
  · exact hs x hx
  · rw [Nat.Prime.primeFactors hℓ, Finset.mem_singleton] at hx
    subst hx
    exact hs x (Nat.mem_primeFactors.mpr ⟨hℓ, hℓd, hd⟩)

/-- **The coprimality of the small-`h` case** (EP1054.tex lines 1753–1756): if `dh ∣ s(n)`, then
every prime factor of `h` avoids `n` and `σ(n)`, because it would divide `gcd(n, σ(n)) = d`, and
then `dℓ` would be a `Y`-smooth divisor of `s(n)` larger than `d`. -/
lemma coprime_of_regAt {Y : ℝ} {d n h : ℕ} (hn : 1 ≤ n) (H : SV.RegularAt Y d n)
    (hdh : d * h ∣ aliquot n) : Nat.Coprime n h ∧ Nat.Coprime (sig n) h := by
  obtain ⟨hd1, hdn, hds, _, _, hsm, hmax, _⟩ := regAt_basic hn H
  have hgcd : d = Nat.gcd n (sig n) := H.1
  have hsig := sig_eq_aliquot_add (n := n) (by omega)
  have hha : h ∣ aliquot n := dvd_trans (Dvd.intro_left d rfl) hdh
  -- no prime factor of `h` divides `d`
  have hnot : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ h → ¬ ℓ ∣ d := by
    intro ℓ hℓ hℓh hℓd
    have h1 : d * ℓ ∣ aliquot n := dvd_trans (Nat.mul_dvd_mul_left d hℓh) hdh
    have h2 := hmax (d * ℓ) h1 (isSmooth_mul_of_dvd (by omega) hℓ hℓd hsm)
    have h3 := hℓ.two_le
    nlinarith
  constructor
  · apply Nat.coprime_of_dvd
    intro ℓ hℓ hℓn hℓh
    apply hnot ℓ hℓ hℓh
    rw [hgcd]
    refine Nat.dvd_gcd hℓn ?_
    rw [hsig]
    exact dvd_add (dvd_trans hℓh hha) hℓn
  · apply Nat.coprime_of_dvd
    intro ℓ hℓ hℓs hℓh
    apply hnot ℓ hℓ hℓh
    have hℓa : ℓ ∣ aliquot n := dvd_trans hℓh hha
    have hℓn : ℓ ∣ n := by
      have := (Nat.dvd_add_right hℓa).mp (hsig ▸ hℓs)
      exact this
    rw [hgcd]
    exact Nat.dvd_gcd hℓn hℓs

end Principia.Erdos1054.Proofs.SvSmallH

namespace Principia.Erdos1054.Proofs

open Finset

theorem leaf_Claim_SvSmallHSquarefree : Principia.Erdos1054.Claim_SvSmallHSquarefree := by
  intro δ _ _ D _ 𝒜 hfam
  obtain ⟨_, _, B, _, X₁, hX₁⟩ := hfam
  refine ⟨max X₁ ((2 : ℝ) ^ 15), ?_⟩
  intro X hX d n n' hC hh
  have hXa : X₁ ≤ X := le_trans (le_max_left _ _) hX
  have hXb : (2 : ℝ) ^ 15 ≤ X := le_trans (le_max_right _ _) hX
  have hX1 : (1 : ℝ) < X := by linarith [show (1 : ℝ) < 2 ^ 15 by norm_num]
  have hX0 : (0 : ℝ) < X := by linarith
  obtain ⟨_, _, hreg⟩ := hX₁ X hXa
  obtain ⟨_, p, p', ⟨q, r, k, hm, rfl⟩, ⟨q', r', k', hm', rfl⟩, _⟩ := hC
  obtain ⟨_, _, hRn, _, hSq, _, _⟩ := SvSmallH.member_regular hreg hm
  obtain ⟨_, _, hRn', _, _, _, _⟩ := SvSmallH.member_regular hreg hm'
  obtain ⟨_, hq, hr, hk, _, _, _, hnlo, _, _⟩ := SvSmallH.tuple_facts hXb hm.1
  obtain ⟨_, hq', hr', hk', _, _, _, _, _, _⟩ := SvSmallH.tuple_facts hXb hm'.1
  have hn1 : 1 ≤ q * r * k := Nat.mul_pos (Nat.mul_pos hq.pos hr.pos) hk
  have hn1' : 1 ≤ q' * r' * k' := Nat.mul_pos (Nat.mul_pos hq'.pos hr'.pos) hk'
  obtain ⟨hd1, _, _, hda, han, _, _, hrough⟩ := SvSmallH.regAt_basic hn1 hRn
  obtain ⟨_, _, _, hda', _, _, _, _⟩ := SvSmallH.regAt_basic hn1' hRn'
  set n := q * r * k with hn
  set g := SV.gcdS n (q' * r' * k') with hg
  have hdg : d ∣ g := Nat.dvd_gcd hda hda'
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero han)
  have hh0 : 0 < g / d := Nat.div_pos (Nat.le_of_dvd hg0 hdg) hd1
  have hhdiv : g / d ∣ aliquot n / d := Nat.div_dvd_div hdg (Nat.gcd_dvd_left _ _)
  have had0 : aliquot n / d ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero han) hda) hd1).ne'
  rw [Nat.squarefree_iff_prime_squarefree]
  intro q₀ hq₀ hdiv
  have hq₀a : q₀ ∣ aliquot n / d := dvd_trans (Dvd.intro q₀ rfl) (dvd_trans hdiv hhdiv)
  have hy : yLP n < (q₀ : ℝ) :=
    hrough q₀ (Nat.mem_primeFactors.mpr ⟨hq₀, hq₀a, had0⟩)
  have hsqd : q₀ ^ 2 ∣ aliquot n := by
    rw [sq]
    exact dvd_trans hdiv (dvd_trans hhdiv (Nat.div_dvd_of_dvd hda))
  have hbig : (n : ℝ) ^ ((10 : ℝ) / 27) < (q₀ : ℝ) := by
    by_contra hcon
    exact hSq q₀ hq₀ hy (not_lt.mp hcon) hsqd
  have hle : q₀ * q₀ ≤ g / d := Nat.le_of_dvd hh0 hdiv
  have hleR : (q₀ : ℝ) ^ 2 ≤ ((g / d : ℕ) : ℝ) := by
    rw [sq]
    exact_mod_cast hle
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
  have c1 : X ^ ((10 : ℝ) / 33) < X ^ ((17 : ℝ) / 54) := SvSmallH.rpow_lt_of_lt hX1 (by norm_num)
  have c2 : X ^ ((17 : ℝ) / 54) < (n : ℝ) ^ ((20 : ℝ) / 27) := by
    have e : X ^ ((17 : ℝ) / 54) = (X ^ ((17 : ℝ) / 40)) ^ ((20 : ℝ) / 27) := by
      rw [← Real.rpow_mul hX0.le]
      norm_num
    rw [e]
    exact Real.rpow_lt_rpow (Real.rpow_nonneg hX0.le _) hnlo (by norm_num)
  have c3 : (n : ℝ) ^ ((20 : ℝ) / 27) < (q₀ : ℝ) ^ 2 := by
    have e : (n : ℝ) ^ ((20 : ℝ) / 27) = ((n : ℝ) ^ ((10 : ℝ) / 27)) ^ 2 := by
      rw [← Real.rpow_mul_natCast hn0]
      norm_num
    rw [e]
    exact pow_lt_pow_left₀ hbig (Real.rpow_nonneg hn0 _) (by norm_num)
  linarith

end Principia.Erdos1054.Proofs

namespace Principia.Erdos1054.Proofs.SvSmallH

open Finset

/-- `σ(qrk) = (q+1)(r+1)σ(k)` for primes `q, r` with `rk < q` and `k < r`. -/
lemma sig_qrk {q r k : ℕ} (hq : q.Prime) (hr : r.Prime) (hk : 1 ≤ k) (hkr : k < r)
    (hrkq : r * k < q) : sig (q * r * k) = (q + 1) * (r + 1) * sig k := by
  have hcop_rk : Nat.Coprime r k := (Nat.Prime.coprime_iff_not_dvd hr).mpr (fun h => by
    have := Nat.le_of_dvd (by omega) h
    omega)
  have hcop_q : Nat.Coprime q (r * k) := (Nat.Prime.coprime_iff_not_dvd hq).mpr (fun h => by
    have := Nat.le_of_dvd (Nat.mul_pos hr.pos (by omega)) h
    omega)
  rw [mul_assoc q r k, sig_mul hcop_q, sig_mul hcop_rk, sig_prime hq, sig_prime hr]
  ring

/-- The identity `s(pn) = p s(n) + σ(n)` for a prime `p ∤ n` (`eq:sv-collision`), proved here from
the definitions (it is the leaf `Eq_SvCollision`). -/
lemma collision_identity {p n : ℕ} (hp : p.Prime) (hpn : ¬ p ∣ n) :
    aliquot (p * n) = p * aliquot n + sig n := by
  have hcop : Nat.Coprime p n := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpn
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hpn (dvd_zero p)
  have h1 : sig (p * n) = (p + 1) * sig n := by rw [sig_mul hcop, sig_prime hp]
  have h2 := le_sig hn0
  unfold aliquot
  rw [h1, Nat.mul_sub]
  have h3 : p * n ≤ p * sig n := Nat.mul_le_mul_left p h2
  zify [h2, h3, show p * n ≤ (p + 1) * sig n by nlinarith]
  ring

/-- The data carried by one `n`-part of a member of the class `d`, for `X ≥ 2^15`: the prime `p`
exceeds `n`, `n ≥ 1`, and (i)–(ii) of `lem:sv-regular` hold at `n`. -/
lemma nPart_facts {D : ℕ} {B X : ℝ} {A : Finset ℕ} (hX : (2 : ℝ) ^ 15 ≤ X)
    (hreg : ∀ M ∈ A, SV.RegularMember D B X M) {d p n : ℕ} (hN : SV.IsNPart D A X d p n) :
    p.Prime ∧ 1 ≤ n ∧ n < p ∧ SV.RegularAt (SV.Ycut X) d n ∧ Eq_SvImageAbundancy B n := by
  obtain ⟨q, r, k, hm, rfl⟩ := hN
  obtain ⟨_, _, hRn, _, _, _, hab⟩ := member_regular hreg hm
  obtain ⟨hp, hq, hr, hk, _, _, hnp, _, _, _⟩ := tuple_facts hX hm.1
  exact ⟨hp, Nat.mul_pos (Nat.mul_pos hq.pos hr.pos) hk, hnp, hRn, hab⟩

/-- The collision congruence data: for a collision pair `(n, n')` with realising primes `p, p'`,
`p s(n) + σ(n) = p' s(n') + σ(n')` in `ℤ`. -/
lemma collision_eq {p n p' n' : ℕ} (hp : p.Prime) (hnp : n < p) (hn : 1 ≤ n) (hp' : p'.Prime)
    (hnp' : n' < p') (hn' : 1 ≤ n') (hcol : aliquot (p * n) = aliquot (p' * n')) :
    (p : ℤ) * (aliquot n : ℤ) + (sig n : ℤ) = (p' : ℤ) * (aliquot n' : ℤ) + (sig n' : ℤ) := by
  have e1 := collision_identity hp (fun h => by have := Nat.le_of_dvd hn h; omega)
  have e2 := collision_identity hp' (fun h => by have := Nat.le_of_dvd hn' h; omega)
  have E0 : p * aliquot n + sig n = p' * aliquot n' + sig n' := by rw [← e1, ← e2]; exact hcol
  exact_mod_cast E0

end Principia.Erdos1054.Proofs.SvSmallH

namespace Principia.Erdos1054.Proofs

open Finset

theorem link_Claim_SvSmallHResidues : Principia.Erdos1054.Spine.Link_Claim_SvSmallHResidues := by
  intro _ δ _ _ D _ 𝒜 hfam
  obtain ⟨_, _, B, _, X₁, hX₁⟩ := hfam
  refine ⟨max X₁ ((2 : ℝ) ^ 15), ?_⟩
  intro X hX d p q r k n' hM hC _
  have hXa : X₁ ≤ X := le_trans (le_max_left _ _) hX
  have hXb : (2 : ℝ) ^ 15 ≤ X := le_trans (le_max_right _ _) hX
  obtain ⟨_, _, hreg⟩ := hX₁ X hXa
  obtain ⟨_, p₁, p₁', hN1, hN2, hcol⟩ := hC
  obtain ⟨hp₁, hn1, hnp₁, hRn, _⟩ := SvSmallH.nPart_facts hXb hreg hN1
  obtain ⟨hp₂, hn1', hnp₂, hRn', _⟩ := SvSmallH.nPart_facts hXb hreg hN2
  obtain ⟨_, hq, hr, hk, hkr, hrkq, _, _, _, _⟩ := SvSmallH.tuple_facts hXb hM.1
  have hsign := SvSmallH.sig_qrk hq hr hk hkr hrkq
  have E := SvSmallH.collision_eq hp₁ hnp₁ hn1 hp₂ hnp₂ hn1' hcol
  set n := q * r * k with hn
  obtain ⟨_, _, _, hda, _, _, _, _⟩ := SvSmallH.regAt_basic hn1 hRn
  obtain ⟨_, _, _, hda', _, _, _, _⟩ := SvSmallH.regAt_basic hn1' hRn'
  have hdg : d ∣ SV.gcdS n n' := Nat.dvd_gcd hda hda'
  have hdh : d * (SV.gcdS n n' / d) ∣ aliquot n := by
    rw [Nat.mul_div_cancel' hdg]
    exact Nat.gcd_dvd_left _ _
  obtain ⟨hcn, hcs⟩ := SvSmallH.coprime_of_regAt hn1 hRn hdh
  set h := SV.gcdS n n' / d with hh
  have hhg : h ∣ SV.gcdS n n' := Nat.div_dvd_of_dvd hdg
  have hA : (h : ℤ) ∣ (aliquot n : ℤ) :=
    Int.natCast_dvd_natCast.mpr (dvd_trans hhg (Nat.gcd_dvd_left _ _))
  have hA' : (h : ℤ) ∣ (aliquot n' : ℤ) :=
    Int.natCast_dvd_natCast.mpr (dvd_trans hhg (Nat.gcd_dvd_right _ _))
  have S1 : (sig n : ℤ) = (aliquot n : ℤ) + n := by
    exact_mod_cast SvSmallH.sig_eq_aliquot_add (n := n) (by omega)
  have S2 : (sig n' : ℤ) = (aliquot n' : ℤ) + n' := by
    exact_mod_cast SvSmallH.sig_eq_aliquot_add (n := n') (by omega)
  refine ⟨Nat.Coprime.coprime_dvd_left (Dvd.intro_left (q * r) rfl) hcn,
    Nat.Coprime.coprime_dvd_left (hsign ▸ Dvd.intro_left _ rfl) hcs, ?_, ?_⟩
  · rw [Nat.modEq_iff_dvd]
    have e : (n' : ℤ) - (n : ℤ) = ((p₁ : ℤ) + 1) * aliquot n - ((p₁' : ℤ) + 1) * aliquot n' := by
      linarith
    rw [e]
    exact dvd_sub (dvd_mul_of_dvd_right hA _) (dvd_mul_of_dvd_right hA' _)
  · rw [Nat.modEq_iff_dvd, ← hsign]
    have e : (n' : ℤ) - (sig n : ℤ) = (p₁ : ℤ) * aliquot n - ((p₁' : ℤ) + 1) * aliquot n' := by
      linarith
    rw [e]
    exact dvd_sub (dvd_mul_of_dvd_right hA _) (dvd_mul_of_dvd_right hA' _)

end Principia.Erdos1054.Proofs

namespace Principia.Erdos1054.Proofs.SvSmallH

open Finset

/-! ## The level `Y` -/

lemma logIt_two (x : ℝ) : logIt 2 x = Real.log (Real.log x) := rfl

lemma logIt_three (x : ℝ) : logIt 3 x = Real.log (Real.log (Real.log x)) := rfl

/-- For `X ≥ e^{360}`: `Y = y(X^{1/120}) ≥ e`, so `log Y ≥ 1` (`L/log L ≥ e` for `L > 1`). -/
lemma Ycut_ge {X : ℝ} (hX : Real.exp 360 ≤ X) :
    Real.exp 1 ≤ SV.Ycut X ∧ 1 ≤ Real.log (SV.Ycut X) := by
  have hX0 : 0 < X := lt_of_lt_of_le (Real.exp_pos _) hX
  have hlX : 360 ≤ Real.log X := by
    rw [← Real.log_exp 360]
    exact Real.log_le_log (Real.exp_pos _) hX
  have hlu : Real.log (X ^ ((1 : ℝ) / 120)) = Real.log X / 120 := by
    rw [Real.log_rpow hX0]
    ring
  have hlu3 : 3 ≤ Real.log (X ^ ((1 : ℝ) / 120)) := by
    rw [hlu]
    linarith
  set L := Real.log (Real.log (X ^ ((1 : ℝ) / 120))) with hLdef
  have h3 : 1 < Real.log 3 := by
    rw [← Real.log_exp 1]
    exact Real.log_lt_log (Real.exp_pos 1) (by have := Real.exp_one_lt_d9; linarith)
  have hL : 1 < L := lt_of_lt_of_le h3 (Real.log_le_log (by norm_num) hlu3)
  have hlogL : 0 < Real.log L := Real.log_pos hL
  have hY : SV.Ycut X = L / Real.log L := rfl
  have key : Real.exp 1 ≤ L / Real.log L := by
    rw [le_div_iff₀ hlogL]
    have h1 := Real.log_le_sub_one_of_pos (show 0 < L / Real.exp 1 by positivity)
    rw [Real.log_div (by linarith) (Real.exp_pos 1).ne', Real.log_exp] at h1
    have h2 : Real.log L ≤ L / Real.exp 1 := by linarith
    rw [le_div_iff₀ (Real.exp_pos 1)] at h2
    linarith
  refine ⟨hY ▸ key, ?_⟩
  rw [hY]
  calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ ≤ Real.log (L / Real.log L) := Real.log_le_log (Real.exp_pos 1) key

/-! ## The second moment as a pair count -/

/-- `∑_u R(u)^2` is the number of pairs `(M, M')` with `s(M) = s(M')`. -/
lemma sum_sq_card_fiber (S : Finset ℕ) (s : ℕ → ℕ) :
    ∑ u ∈ S.image s, ((S.filter (fun M => s M = u)).card) ^ 2 =
      ((S ×ˢ S).filter (fun x : ℕ × ℕ => s x.1 = s x.2)).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun x : ℕ × ℕ => s x.1) (t := S.image s)]
  · apply Finset.sum_congr rfl
    intro u _
    rw [sq, ← Finset.card_product]
    congr 1
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_product]
    constructor
    · intro h
      exact ⟨⟨⟨h.1.1, h.2.1⟩, h.1.2.trans h.2.2.symm⟩, h.1.2⟩
    · intro h
      exact ⟨⟨h.1.1.1, h.2⟩, ⟨h.1.1.2, h.1.2 ▸ h.2⟩⟩
  · intro x hx
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hx
    exact Finset.mem_image_of_mem s hx.1.1

end Principia.Erdos1054.Proofs.SvSmallH

namespace Principia.Erdos1054.Proofs

open Finset

theorem link_Prop_SvSecondMoment : Principia.Erdos1054.Spine.Link_Prop_SvSecondMoment := by
  intro _ hsieve htot hA3 hred
  classical
  obtain ⟨C₃, hA3'⟩ := hA3
  intro δ hδ hδ1 D hD 𝒜 hfam c c₁ c₂ c₃ hc hc₁ hc₂ hc₃
  obtain ⟨Cs, Xs, hs⟩ := hsieve δ hδ hδ1 D hD 𝒜 hfam
  obtain ⟨X₃, h3⟩ := hA3' δ hδ hδ1 D hD 𝒜 hfam
  obtain ⟨Cr, Xr, hr⟩ := hred δ hδ hδ1 D hD 𝒜 hfam c c₁ c₂ c₃ hc hc₁ hc₂ hc₃
  obtain ⟨_, _, B, hB, X₁, hX₁⟩ := hfam
  set K : ℝ := Real.pi ^ 2 / 6 * B with hK
  set κ : ℝ := max Cs 0 * K * K * C₃ with hκ
  refine ⟨c₂ + max κ 0 * Cr,
    max (max (max X₁ ((2 : ℝ) ^ 15)) (max Xs X₃)) (max Xr (Real.exp 360)), ?_⟩
  intro X hX 𝒟 hcl d hd
  have hXa : X₁ ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_trans (le_max_left _ _) hX)
  have hXb : (2 : ℝ) ^ 15 ≤ X :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_trans (le_max_left _ _) hX)
  have hXs : Xs ≤ X :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_trans (le_max_left _ _) hX)
  have hX3 : X₃ ≤ X :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_trans (le_max_left _ _) hX)
  have hXr : Xr ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hX
  have hXe : Real.exp 360 ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hX
  have hX0 : 0 < X := lt_of_lt_of_le (by positivity) hXb
  obtain ⟨hsub, _, hreg⟩ := hX₁ X hXa
  obtain ⟨_, hlogY⟩ := SvSmallH.Ycut_ge hXe
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith [show (1 : ℝ) < 2 ^ 15 by norm_num])
  have hd1 : 1 ≤ d := (hcl.1 d hd).1
  set Y := SV.Ycut X with hYdef
  set W : ℝ := X / ((d : ℝ) * Real.log Y) with hW
  have hW0 : 0 ≤ W := by
    rw [hW]
    apply div_nonneg hX0.le
    apply mul_nonneg (by positivity) (by linarith)
  set S := SV.classFin (𝒜 X) X d with hSdef
  have hScard : (S.card : ℝ) ≤ c₂ * W := (hcl.2.1.1 d hd).2
  -- every member of the class has a tuple
  have hch : ∀ M ∈ S, ∃ pn : ℕ × ℕ, SV.IsNPart D (𝒜 X) X d pn.1 pn.2 ∧ M = pn.1 * pn.2 ∧
      M ≤ ⌊X⌋₊ := by
    intro M hM
    rw [hSdef, SV.classFin, Finset.mem_filter] at hM
    have hM0 := hsub hM.1
    simp only [S4a.A0, Finset.mem_filter, Finset.mem_Icc] at hM0
    obtain ⟨⟨_, hMX⟩, p, q, r, k, ht, rfl⟩ := hM0
    refine ⟨(p, q * r * k), ⟨q, r, k, ⟨ht, hM.1, hM.2⟩, rfl⟩, by ring, hMX⟩
  choose! φ hφ using hch
  -- the facts attached to each member
  have hfact : ∀ M ∈ S, (φ M).1.Prime ∧ 1 ≤ (φ M).2 ∧ (φ M).2 < (φ M).1 ∧
      aliquot (φ M).2 ≠ 0 ∧ (φ M).1 ≤ ⌊X⌋₊ ∧ (φ M).2 ≤ ⌊X⌋₊ := by
    intro M hM
    obtain ⟨hN, hMe, hMX⟩ := hφ M hM
    obtain ⟨hp, hn1, hnp, hRn, _⟩ := SvSmallH.nPart_facts hXb hreg hN
    obtain ⟨_, _, _, _, han, _, _, _⟩ := SvSmallH.regAt_basic hn1 hRn
    refine ⟨hp, hn1, hnp, han, ?_, ?_⟩
    · calc (φ M).1 ≤ (φ M).1 * (φ M).2 := Nat.le_mul_of_pos_right _ (by omega)
        _ = M := hMe.symm
        _ ≤ ⌊X⌋₊ := hMX
    · calc (φ M).2 ≤ (φ M).1 * (φ M).2 := Nat.le_mul_of_pos_left _ hp.pos
        _ = M := hMe.symm
        _ ≤ ⌊X⌋₊ := hMX
  set box := Finset.Icc 1 ⌊X⌋₊ ×ˢ Finset.Icc 1 ⌊X⌋₊ with hbox
  set E := box.filter (fun nn : ℕ × ℕ => SV.CollisionPair D (𝒜 X) X d nn.1 nn.2) with hE
  set PS : ℕ × ℕ → Finset (ℕ × ℕ) := fun nn => box.filter (fun pp : ℕ × ℕ =>
    SV.IsNPart D (𝒜 X) X d pp.1 nn.1 ∧ SV.IsNPart D (𝒜 X) X d pp.2 nn.2 ∧
      aliquot (pp.1 * nn.1) = aliquot (pp.2 * nn.2)) with hPS
  have hPScard : ∀ nn : ℕ × ℕ, ((PS nn).card : ℝ) = (SV.pairCount D (𝒜 X) X d nn.1 nn.2 : ℝ) := by
    intro nn
    unfold SV.pairCount
    congr 2
  set P := (S ×ˢ S).filter (fun x : ℕ × ℕ => aliquot x.1 = aliquot x.2) with hP
  -- (1) the second moment is `#P`
  have hmom : ∑ u ∈ S.image aliquot, ((SV.Rd (𝒜 X) X d u : ℕ) : ℝ) ^ 2 = (P.card : ℝ) := by
    have := SvSmallH.sum_sq_card_fiber S aliquot
    unfold SV.Rd
    exact_mod_cast this
  -- (2) diagonal and off-diagonal
  have hsplit : P.card = (P.filter (fun x => x.1 = x.2)).card +
      (P.filter (fun x => ¬ x.1 = x.2)).card :=
    (Finset.card_filter_add_card_filter_not (fun x : ℕ × ℕ => x.1 = x.2)).symm
  have hdiag : (P.filter (fun x => x.1 = x.2)).card ≤ S.card := by
    refine Finset.card_le_card_of_injOn Prod.fst ?_ ?_
    · intro x hx
      rw [Finset.mem_coe, Finset.mem_filter, hP, Finset.mem_filter, Finset.mem_product] at hx
      exact hx.1.1.1
    · intro x hx y hy hxy
      rw [Finset.mem_coe, Finset.mem_filter] at hx hy
      exact Prod.ext hxy (by rw [← hx.2, ← hy.2]; exact hxy)
  -- (3) the off-diagonal pairs inject into the realised prime pairs of collision pairs
  have hoff : (P.filter (fun x => ¬ x.1 = x.2)).card ≤ ∑ nn ∈ E, (PS nn).card := by
    have himg : ∀ nn : ℕ × ℕ, ((PS nn).image (fun pp => (nn, pp))).card = (PS nn).card :=
      fun nn => Finset.card_image_of_injective _ (fun a b hab => (Prod.mk.inj hab).2)
    refine le_trans ?_ (le_trans Finset.card_biUnion_le
      (le_of_eq (Finset.sum_congr rfl (fun nn _ => himg nn))))
    refine Finset.card_le_card_of_injOn
      (fun x : ℕ × ℕ => (((φ x.1).2, (φ x.2).2), ((φ x.1).1, (φ x.2).1))) ?_ ?_
    · intro x hx
      rw [Finset.mem_coe, Finset.mem_filter, hP, Finset.mem_filter, Finset.mem_product] at hx
      obtain ⟨⟨⟨hM, hM'⟩, hsM⟩, hne⟩ := hx
      obtain ⟨hN, hMe, _⟩ := hφ x.1 hM
      obtain ⟨hN', hMe', _⟩ := hφ x.2 hM'
      obtain ⟨hp, hn1, hnp, han, hpX, hnX⟩ := hfact x.1 hM
      obtain ⟨hp', hn1', hnp', _, hpX', hnX'⟩ := hfact x.2 hM'
      have hcolM : aliquot ((φ x.1).1 * (φ x.1).2) = aliquot ((φ x.2).1 * (φ x.2).2) := by
        rw [← hMe, ← hMe']
        exact hsM
      rw [Finset.mem_coe, Finset.mem_biUnion]
      refine ⟨((φ x.1).2, (φ x.2).2), ?_, ?_⟩
      · rw [hE, Finset.mem_filter, hbox, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
        refine ⟨⟨⟨hn1, hnX⟩, ⟨hn1', hnX'⟩⟩, ?_, (φ x.1).1, (φ x.2).1, hN, hN', hcolM⟩
        -- `n ≠ n'`
        intro hnn
        apply hne
        have E1 := SvSmallH.collision_eq hp hnp hn1 hp' hnp' hn1' hcolM
        simp only at hnn
        rw [← hnn] at E1
        have hpp : ((φ x.1).1 : ℤ) = (φ x.2).1 := by
          have h1 : (((φ x.1).1 : ℤ) - (φ x.2).1) * (aliquot (φ x.1).2 : ℤ) = 0 := by linarith
          rcases mul_eq_zero.mp h1 with h | h
          · linarith
          · exact absurd (by exact_mod_cast h) han
        have hpp' : (φ x.1).1 = (φ x.2).1 := by exact_mod_cast hpp
        rw [hMe, hMe', hpp', hnn]
      · rw [Finset.mem_image]
        refine ⟨((φ x.1).1, (φ x.2).1), ?_, rfl⟩
        rw [hPS]
        simp only
        rw [Finset.mem_filter, hbox, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
        exact ⟨⟨⟨hp.one_lt.le, hpX⟩, ⟨hp'.one_lt.le, hpX'⟩⟩, hN, hN', hcolM⟩
    · intro x hx y hy hxy
      rw [Finset.mem_coe, Finset.mem_filter, hP, Finset.mem_filter, Finset.mem_product] at hx hy
      simp only [Prod.mk.injEq] at hxy
      obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hxy
      have e1 : x.1 = y.1 := by rw [(hφ x.1 hx.1.1.1).2.1, (hφ y.1 hy.1.1.1).2.1, h1, h3]
      have e2 : x.2 = y.2 := by rw [(hφ x.2 hx.1.1.2).2.1, (hφ y.2 hy.1.1.2).2.1, h2, h4]
      exact Prod.ext e1 e2
  -- (4) the sieve bound for each collision pair
  have hpair : ∀ nn ∈ E, ((PS nn).card : ℝ) ≤
      κ * (X * Real.log Y / Real.log X ^ 2 *
        ((SV.gcdS nn.1 nn.2 : ℝ) / ((nn.1 : ℝ) * (nn.2 : ℝ)) * SV.ratio32 X nn.1 nn.2)) := by
    intro nn hnn
    rw [hE, Finset.mem_filter] at hnn
    have hC := hnn.2
    obtain ⟨_, p, p', hN, hN', _⟩ := hnn.2
    obtain ⟨_, hn1, _, hRn, hab⟩ := SvSmallH.nPart_facts hXb hreg hN
    obtain ⟨_, hn1', _, hRn', hab'⟩ := SvSmallH.nPart_facts hXb hreg hN'
    obtain ⟨_, _, _, _, han, _, _, _⟩ := SvSmallH.regAt_basic hn1 hRn
    obtain ⟨_, _, _, _, han', _, _, _⟩ := SvSmallH.regAt_basic hn1' hRn'
    set g := SV.gcdS nn.1 nn.2 with hg
    have hg0 : 0 < g := Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero han)
    -- the `A_1, A_2` factors
    have hA : ∀ m : ℕ, aliquot m ≠ 0 → g ∣ aliquot m → Eq_SvImageAbundancy B m →
        SV.phiRatio (aliquot m / g) ≤ K := by
      intro m hm0 hgm hB'
      have hv1 : 1 ≤ aliquot m / g :=
        Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) hgm) hg0
      obtain ⟨t1, t2⟩ := htot (aliquot m / g) (aliquot m) hv1 (Nat.pos_of_ne_zero hm0)
        (Nat.div_dvd_of_dvd hgm)
      unfold SV.phiRatio
      calc ((aliquot m / g : ℕ) : ℝ) / ((aliquot m / g).totient : ℝ)
          ≤ Real.pi ^ 2 / 6 * abundancy (aliquot m / g) := t1
        _ ≤ Real.pi ^ 2 / 6 * abundancy (aliquot m) :=
            mul_le_mul_of_nonneg_left t2 (by positivity)
        _ ≤ Real.pi ^ 2 / 6 * B := mul_le_mul_of_nonneg_left hB' (by positivity)
    have hA1 := hA nn.1 han (Nat.gcd_dvd_left _ _) hab
    have hA2 := hA nn.2 han' (Nat.gcd_dvd_right _ _) hab'
    have hphi_nn : ∀ m : ℕ, 0 ≤ SV.phiRatio m := fun m => by
      unfold SV.phiRatio
      positivity
    have hsv := hs X hXs d nn.1 nn.2 hC
    have h3v := h3 X hX3 d nn.1 nn.2 hC
    have hT : 0 ≤ X * (g : ℝ) / ((nn.1 : ℝ) * (nn.2 : ℝ) * Real.log X ^ 2) := by positivity
    have hcs : ((PS nn).card : ℝ) ≤ max Cs 0 * (X * (g : ℝ) / ((nn.1 : ℝ) * (nn.2 : ℝ) *
        Real.log X ^ 2)) * SV.phiRatio (aliquot nn.1 / g) * SV.phiRatio (aliquot nn.2 / g) *
        SV.phiRatio (SV.A3 nn.1 nn.2) := by
      rw [hPScard]
      refine le_trans hsv ?_
      have := hphi_nn (aliquot nn.1 / g)
      have := hphi_nn (aliquot nn.2 / g)
      have := hphi_nn (SV.A3 nn.1 nn.2)
      gcongr
      exact le_max_left _ _
    have hK0 : 0 ≤ K := by positivity
    calc ((PS nn).card : ℝ)
        ≤ max Cs 0 * (X * (g : ℝ) / ((nn.1 : ℝ) * (nn.2 : ℝ) * Real.log X ^ 2)) *
            SV.phiRatio (aliquot nn.1 / g) * SV.phiRatio (aliquot nn.2 / g) *
            SV.phiRatio (SV.A3 nn.1 nn.2) := hcs
      _ ≤ max Cs 0 * (X * (g : ℝ) / ((nn.1 : ℝ) * (nn.2 : ℝ) * Real.log X ^ 2)) * K * K *
            (C₃ * Real.log Y * SV.ratio32 X nn.1 nn.2) := by
          have := hphi_nn (aliquot nn.2 / g)
          have := hphi_nn (SV.A3 nn.1 nn.2)
          have hm0 : 0 ≤ max Cs 0 := le_max_right _ _
          gcongr
      _ = κ * (X * Real.log Y / Real.log X ^ 2 *
            ((g : ℝ) / ((nn.1 : ℝ) * (nn.2 : ℝ)) * SV.ratio32 X nn.1 nn.2)) := by
          rw [hκ]
          ring
  -- (5) the reduced collision sum
  have hRCS : SV.reducedCollisionSum D (𝒜 X) X d (fun _ => True) =
      ∑ nn ∈ E, (SV.gcdS nn.1 nn.2 : ℝ) / ((nn.1 : ℝ) * (nn.2 : ℝ)) * SV.ratio32 X nn.1 nn.2 := by
    unfold SV.reducedCollisionSum
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext x
    simp only [hE, hbox, Finset.mem_filter, and_true]
  have hr' := hr X hXr 𝒟 hcl d hd
  rw [hRCS] at hr'
  have hratio_nn : ∀ nn ∈ E, 0 ≤ (SV.gcdS nn.1 nn.2 : ℝ) / ((nn.1 : ℝ) * (nn.2 : ℝ)) *
      SV.ratio32 X nn.1 nn.2 := by
    intro nn _
    apply mul_nonneg (by positivity)
    unfold SV.ratio32
    apply Finset.prod_nonneg
    intro p hp
    rw [Finset.mem_filter] at hp
    have := (Nat.prime_of_mem_primeFactors hp.1).two_le
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast this
    apply div_nonneg <;> linarith
  have hZ0 : 0 ≤ X * Real.log Y / Real.log X ^ 2 *
      ∑ nn ∈ E, (SV.gcdS nn.1 nn.2 : ℝ) / ((nn.1 : ℝ) * (nn.2 : ℝ)) * SV.ratio32 X nn.1 nn.2 := by
    apply mul_nonneg (by positivity) (Finset.sum_nonneg hratio_nn)
  -- assemble
  have hr'' : X * Real.log Y / Real.log X ^ 2 *
      (∑ nn ∈ E, (SV.gcdS nn.1 nn.2 : ℝ) / ((nn.1 : ℝ) * (nn.2 : ℝ)) * SV.ratio32 X nn.1 nn.2) ≤
      Cr * W := hr'
  unfold Eq_SvSecondMoment
  rw [← hSdef, hmom]
  have hPc : (P.card : ℝ) ≤ (S.card : ℝ) + ∑ nn ∈ E, ((PS nn).card : ℝ) := by
    have := le_trans (le_of_eq hsplit) (Nat.add_le_add hdiag hoff)
    exact_mod_cast this
  calc (P.card : ℝ) ≤ (S.card : ℝ) + ∑ nn ∈ E, ((PS nn).card : ℝ) := hPc
    _ ≤ c₂ * W + ∑ nn ∈ E, κ * (X * Real.log Y / Real.log X ^ 2 *
          ((SV.gcdS nn.1 nn.2 : ℝ) / ((nn.1 : ℝ) * (nn.2 : ℝ)) * SV.ratio32 X nn.1 nn.2)) :=
        add_le_add hScard (Finset.sum_le_sum hpair)
    _ = c₂ * W + κ * (X * Real.log Y / Real.log X ^ 2 *
          ∑ nn ∈ E, (SV.gcdS nn.1 nn.2 : ℝ) / ((nn.1 : ℝ) * (nn.2 : ℝ)) *
            SV.ratio32 X nn.1 nn.2) := by
        rw [← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ c₂ * W + max κ 0 * (X * Real.log Y / Real.log X ^ 2 *
          ∑ nn ∈ E, (SV.gcdS nn.1 nn.2 : ℝ) / ((nn.1 : ℝ) * (nn.2 : ℝ)) *
            SV.ratio32 X nn.1 nn.2) := by
        gcongr
        exact le_max_left _ _
    _ ≤ c₂ * W + max κ 0 * (Cr * W) := by
        gcongr
    _ = (c₂ + max κ 0 * Cr) * W := by ring

end Principia.Erdos1054.Proofs

namespace Principia.Erdos1054.Proofs.SvSmallH

open Finset

/-! ## Products `∏ p/(p−1)`, reciprocal prime sums, Mertens on an interval -/

lemma ratio_le_exp {p : ℕ} (hp : 2 ≤ p) : (p : ℝ) / ((p : ℝ) - 1) ≤ Real.exp (1 / ((p : ℝ) - 1)) := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hne : (p : ℝ) - 1 ≠ 0 := by linarith
  have e : (p : ℝ) / ((p : ℝ) - 1) = 1 / ((p : ℝ) - 1) + 1 := by
    rw [div_add_one hne]
    congr 1
    ring
  rw [e]
  exact Real.add_one_le_exp _

lemma prod_ratio_le_exp (I : Finset ℕ) (hI : ∀ p ∈ I, 2 ≤ p) :
    ∏ p ∈ I, (p : ℝ) / ((p : ℝ) - 1) ≤ Real.exp (∑ p ∈ I, 1 / ((p : ℝ) - 1)) := by
  rw [Real.exp_sum]
  apply Finset.prod_le_prod
  · intro p hp
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hI p hp
    apply div_nonneg <;> linarith
  · intro p hp
    exact ratio_le_exp (hI p hp)

lemma inv_sub_one_le_two_div {p : ℕ} (hp : 2 ≤ p) : 1 / ((p : ℝ) - 1) ≤ 2 / p := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  linarith

lemma inv_sub_one_le {p : ℕ} (hp : 2 ≤ p) : 1 / ((p : ℝ) - 1) ≤ 1 / p + 2 * ((p : ℝ) ^ 2)⁻¹ := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hp1 : (0 : ℝ) < p - 1 := by linarith
  have e : 1 / (p : ℝ) + 2 * ((p : ℝ) ^ 2)⁻¹ - 1 / ((p : ℝ) - 1) =
      ((p : ℝ) - 2) / ((p : ℝ) ^ 2 * ((p : ℝ) - 1)) := by
    field_simp
    ring
  have : 0 ≤ ((p : ℝ) - 2) / ((p : ℝ) ^ 2 * ((p : ℝ) - 1)) :=
    div_nonneg (by linarith) (by positivity)
  linarith

/-- `∑_{p ∈ I} p^{-2} ≤ 2/(k+1)` when every element of `I` exceeds `k`. -/
lemma sum_inv_sq_le (I : Finset ℕ) (k : ℕ) (hI : ∀ p ∈ I, k < p) :
    ∑ p ∈ I, ((p : ℝ) ^ 2)⁻¹ ≤ 2 / ((k : ℝ) + 1) := by
  calc ∑ p ∈ I, ((p : ℝ) ^ 2)⁻¹ ≤ ∑ i ∈ Finset.Ioo k (I.sup id + 1), ((i : ℝ) ^ 2)⁻¹ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro p hp
          rw [Finset.mem_Ioo]
          exact ⟨hI p hp, Nat.lt_succ_of_le (Finset.le_sup (f := id) hp)⟩
        · intro i _ _
          positivity
    _ ≤ 2 / ((k : ℝ) + 1) := sum_Ioo_inv_sq_le k _

/-- **Mertens' second theorem on an interval** (from `Std_Mertens2`):
`∑_{a<p≤b} 1/p ≤ log log b − log log a + K/log a` for `2 ≤ a ≤ b`. -/
lemma mertens_interval (hM : Std_Mertens2) : ∃ K : ℝ, 0 ≤ K ∧ ∀ a b : ℝ, 2 ≤ a → a ≤ b →
    ∑ p ∈ SV.primesIoc a b, (1 : ℝ) / p ≤
      Real.log (Real.log b) - Real.log (Real.log a) + K / Real.log a := by
  obtain ⟨M, C, h⟩ := hM
  refine ⟨2 * |C|, by positivity, ?_⟩
  intro a b ha hab
  have hb : 2 ≤ b := le_trans ha hab
  have hla : 0 < Real.log a := Real.log_pos (by linarith)
  have hlb : Real.log a ≤ Real.log b := Real.log_le_log (by linarith) hab
  have Ha := h a ha
  have Hb := h b hb
  rw [abs_le] at Ha Hb
  have hsplit : ∑ p ∈ SV.primesIoc a b, (1 : ℝ) / p +
      ∑ p ∈ (Finset.Iic ⌊a⌋₊).filter Nat.Prime, (1 : ℝ) / p ≤
      ∑ p ∈ (Finset.Iic ⌊b⌋₊).filter Nat.Prime, (1 : ℝ) / p := by
    rw [← Finset.sum_union]
    · apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        rw [Finset.mem_union] at hp
        rw [Finset.mem_filter, Finset.mem_Iic]
        rcases hp with hp | hp
        · unfold SV.primesIoc at hp
          rw [Finset.mem_filter, Finset.mem_Iic] at hp
          exact ⟨hp.1, hp.2.1⟩
        · rw [Finset.mem_filter, Finset.mem_Iic] at hp
          exact ⟨le_trans hp.1 (Nat.floor_mono hab), hp.2⟩
      · intro i _ _
        positivity
    · rw [Finset.disjoint_left]
      intro p hp hp'
      unfold SV.primesIoc at hp
      rw [Finset.mem_filter] at hp hp'
      rw [Finset.mem_Iic] at hp'
      have h1 : (p : ℝ) ≤ a := le_trans (Nat.cast_le.mpr hp'.1) (Nat.floor_le (by linarith))
      linarith [hp.2.2]
  have hCa : C / Real.log a ≤ |C| / Real.log a := div_le_div_of_nonneg_right (le_abs_self C) hla.le
  have hCa' : -C / Real.log a ≤ |C| / Real.log a :=
    div_le_div_of_nonneg_right (neg_le_abs C) hla.le
  have hCb : C / Real.log b ≤ |C| / Real.log a := by
    calc C / Real.log b ≤ |C| / Real.log b :=
          div_le_div_of_nonneg_right (le_abs_self C) (by linarith)
      _ ≤ |C| / Real.log a := div_le_div_of_nonneg_left (abs_nonneg C) hla hlb
  have e2 : 2 * |C| / Real.log a = |C| / Real.log a + |C| / Real.log a := by ring
  have e3 : -C / Real.log a = -(C / Real.log a) := by ring
  linarith

/-- `(log t)^2 ≤ t` for `t ≥ 256`. -/
lemma log_sq_le {t : ℝ} (ht : 256 ≤ t) : Real.log t ^ 2 ≤ t := by
  have ht0 : 0 ≤ t := by linarith
  have h1 : Real.log t ≤ t ^ ((1 : ℝ) / 4) / (1 / 4) := Real.log_le_rpow_div ht0 (by norm_num)
  have hl0 : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
  have h2 : Real.log t ^ 2 ≤ 16 * t ^ ((1 : ℝ) / 2) := by
    have e : (t ^ ((1 : ℝ) / 4) / (1 / 4)) ^ 2 = 16 * t ^ ((1 : ℝ) / 2) := by
      rw [div_pow, ← Real.rpow_natCast, ← Real.rpow_mul ht0]
      norm_num
      ring
    calc Real.log t ^ 2 ≤ (t ^ ((1 : ℝ) / 4) / (1 / 4)) ^ 2 := pow_le_pow_left₀ hl0 h1 2
      _ = 16 * t ^ ((1 : ℝ) / 2) := e
  have h3 : (16 : ℝ) ≤ t ^ ((1 : ℝ) / 2) := by
    have e : ((16 : ℝ) ^ 2) ^ ((1 : ℝ) / 2) = 16 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      norm_num
    calc (16 : ℝ) = ((16 : ℝ) ^ 2) ^ ((1 : ℝ) / 2) := e.symm
      _ ≤ t ^ ((1 : ℝ) / 2) := Real.rpow_le_rpow (by norm_num) (by linarith) (by norm_num)
  have h4 : t = t ^ ((1 : ℝ) / 2) * t ^ ((1 : ℝ) / 2) := by
    rw [← Real.rpow_add' ht0 (by norm_num)]
    norm_num
  have h5 : 0 ≤ t ^ ((1 : ℝ) / 2) := Real.rpow_nonneg ht0 _
  nlinarith

/-- The size facts about the iterated logarithms used in the small-`h` case, for
`X ≥ exp(120 e^3)`: `log Y ≥ 1`, `log Y ≤ log log log X`, `log log X ≥ 3`, `log X ≥ 480`. -/
lemma logY_facts {X : ℝ} (hX : Real.exp (120 * Real.exp 3) ≤ X) :
    1 ≤ Real.log (SV.Ycut X) ∧ Real.log (SV.Ycut X) ≤ logIt 3 X ∧ 3 ≤ logIt 2 X ∧
      480 ≤ Real.log X ∧ 1 ≤ logIt 3 X := by
  have he3 : 4 ≤ Real.exp 3 := by
    have := Real.add_one_le_exp (3 : ℝ)
    linarith
  have hX0 : 0 < X := lt_of_lt_of_le (Real.exp_pos _) hX
  have hlX : 120 * Real.exp 3 ≤ Real.log X := by
    rw [← Real.log_exp (120 * Real.exp 3)]
    exact Real.log_le_log (Real.exp_pos _) hX
  have hX360 : Real.exp 360 ≤ X := le_trans (Real.exp_le_exp.mpr (by linarith)) hX
  obtain ⟨_, hY1⟩ := Ycut_ge hX360
  have hlu : Real.log (X ^ ((1 : ℝ) / 120)) = Real.log X / 120 := by
    rw [Real.log_rpow hX0]
    ring
  set u := X ^ ((1 : ℝ) / 120) with hu
  have hlu3 : Real.exp 3 ≤ Real.log u := by rw [hlu]; linarith
  have hL2u : 3 ≤ Real.log (Real.log u) := by
    rw [← Real.log_exp 3]
    exact Real.log_le_log (Real.exp_pos 3) hlu3
  have h3 : 1 < Real.log 3 := by
    rw [← Real.log_exp 1]
    exact Real.log_lt_log (Real.exp_pos 1) (by have := Real.exp_one_lt_d9; linarith)
  have hL3u : 1 < Real.log (Real.log (Real.log u)) :=
    lt_of_lt_of_le h3 (Real.log_le_log (by norm_num) hL2u)
  have hY : SV.Ycut X = Real.log (Real.log u) / Real.log (Real.log (Real.log u)) := rfl
  have hlogY : Real.log (SV.Ycut X) ≤ Real.log (Real.log (Real.log u)) := by
    rw [hY, Real.log_div (by linarith) (by linarith)]
    have : 0 ≤ Real.log (Real.log (Real.log (Real.log u))) := Real.log_nonneg hL3u.le
    linarith
  have hmono1 : Real.log u ≤ Real.log X := by rw [hlu]; linarith
  have hmono2 : Real.log (Real.log u) ≤ Real.log (Real.log X) :=
    Real.log_le_log (by linarith) hmono1
  have hmono3 : Real.log (Real.log (Real.log u)) ≤ Real.log (Real.log (Real.log X)) :=
    Real.log_le_log (by linarith) hmono2
  refine ⟨hY1, le_trans hlogY hmono3, le_trans hL2u hmono2, by linarith, ?_⟩
  exact le_trans hL3u.le hmono3

/-- **The core of `eq:sv-intermediate-totient`.** If `I ⊆ P`, `I ⊆ J` (sets of integers `≥ 2`),
`∑_{p∈P} 1/p ≤ S₀` and `e^{S₀+4} ≤ L`, then `∏_{p∈I} p/(p−1) ≤ e^2 (1 + L ∑_{p∈J} 1/p)`.
(Case `∑_J ≤ 1`: `∏ ≤ exp(2∑_I 1/p) ≤ e^2`. Case `∑_J > 1`: `∏ ≤ exp(∑_P 1/(p−1)) ≤ e^{S₀+4}`.) -/
lemma totient_core (I P J : Finset ℕ) (hIP : I ⊆ P) (hIJ : I ⊆ J) (hP2 : ∀ p ∈ P, 2 ≤ p)
    {S₀ L : ℝ} (hPsum : ∑ p ∈ P, (1 : ℝ) / p ≤ S₀)
    (hBig : Real.exp (S₀ + 4) ≤ L) :
    ∏ p ∈ I, (p : ℝ) / ((p : ℝ) - 1) ≤ Real.exp 2 * (1 + L * ∑ p ∈ J, (1 : ℝ) / p) := by
  have hI2 : ∀ p ∈ I, 2 ≤ p := fun p hp => hP2 p (hIP hp)
  have hL0 : 0 ≤ L := le_trans (Real.exp_pos _).le hBig
  have hJ0 : 0 ≤ ∑ p ∈ J, (1 : ℝ) / p := Finset.sum_nonneg (fun p _ => by positivity)
  have hprod := prod_ratio_le_exp I hI2
  have hInn : ∀ p ∈ I, 0 ≤ 1 / ((p : ℝ) - 1) := by
    intro p hp
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hI2 p hp
    apply div_nonneg <;> linarith
  by_cases hcase : ∑ p ∈ J, (1 : ℝ) / p ≤ 1
  · have h1 : ∑ p ∈ I, 1 / ((p : ℝ) - 1) ≤ 2 * ∑ p ∈ J, (1 : ℝ) / p := by
      calc ∑ p ∈ I, 1 / ((p : ℝ) - 1) ≤ ∑ p ∈ I, 2 / (p : ℝ) :=
            Finset.sum_le_sum (fun p hp => inv_sub_one_le_two_div (hI2 p hp))
        _ = 2 * ∑ p ∈ I, (1 : ℝ) / p := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl (fun p _ => by ring)
        _ ≤ 2 * ∑ p ∈ J, (1 : ℝ) / p := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            exact Finset.sum_le_sum_of_subset_of_nonneg hIJ (fun p _ _ => by positivity)
    calc ∏ p ∈ I, (p : ℝ) / ((p : ℝ) - 1) ≤ Real.exp (∑ p ∈ I, 1 / ((p : ℝ) - 1)) := hprod
      _ ≤ Real.exp 2 := Real.exp_le_exp.mpr (by linarith)
      _ ≤ Real.exp 2 * (1 + L * ∑ p ∈ J, (1 : ℝ) / p) := by
          have : 0 ≤ L * ∑ p ∈ J, (1 : ℝ) / p := mul_nonneg hL0 hJ0
          have he : 0 < Real.exp 2 := Real.exp_pos 2
          nlinarith
  · replace hcase := not_le.mp hcase
    have hPnn : ∀ p ∈ P, 0 ≤ 1 / ((p : ℝ) - 1) := by
      intro p hp
      have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hP2 p hp
      apply div_nonneg <;> linarith
    have h1 : ∑ p ∈ I, 1 / ((p : ℝ) - 1) ≤ S₀ + 4 := by
      calc ∑ p ∈ I, 1 / ((p : ℝ) - 1) ≤ ∑ p ∈ P, 1 / ((p : ℝ) - 1) :=
            Finset.sum_le_sum_of_subset_of_nonneg hIP (fun p hp _ => hPnn p hp)
        _ ≤ ∑ p ∈ P, ((1 : ℝ) / p + 2 * ((p : ℝ) ^ 2)⁻¹) :=
            Finset.sum_le_sum (fun p hp => inv_sub_one_le (hP2 p hp))
        _ = ∑ p ∈ P, (1 : ℝ) / p + 2 * ∑ p ∈ P, ((p : ℝ) ^ 2)⁻¹ := by
            rw [Finset.sum_add_distrib, Finset.mul_sum]
        _ ≤ S₀ + 2 * (2 / ((0 : ℕ) + 1 : ℝ)) := by
            have := sum_inv_sq_le P 0 (fun p hp => by have := hP2 p hp; omega)
            push_cast at this ⊢
            linarith
        _ = S₀ + 4 := by norm_num
    calc ∏ p ∈ I, (p : ℝ) / ((p : ℝ) - 1) ≤ Real.exp (∑ p ∈ I, 1 / ((p : ℝ) - 1)) := hprod
      _ ≤ Real.exp (S₀ + 4) := Real.exp_le_exp.mpr h1
      _ ≤ L := hBig
      _ ≤ L * ∑ p ∈ J, (1 : ℝ) / p := le_mul_of_one_le_right hL0 hcase.le
      _ ≤ Real.exp 2 * (1 + L * ∑ p ∈ J, (1 : ℝ) / p) := by
          have : 0 ≤ L * ∑ p ∈ J, (1 : ℝ) / p := mul_nonneg hL0 hJ0
          have he : 1 ≤ Real.exp 2 := Real.one_le_exp (by norm_num)
          nlinarith

end Principia.Erdos1054.Proofs.SvSmallH

namespace Principia.Erdos1054.Proofs

open Finset

theorem link_Eq_SvIntermediateTotient :
    Principia.Erdos1054.Spine.Link_Eq_SvIntermediateTotient := by
  intro _hColl hM2 δ _ _ D _ 𝒜 hfam
  obtain ⟨K, hK0, hK⟩ := SvSmallH.mertens_interval hM2
  obtain ⟨_, _, B, _, X₁, hX₁⟩ := hfam
  refine ⟨Real.exp 2 * max 1 (Real.exp (K + 4) / 2),
    max (max X₁ ((2 : ℝ) ^ 15)) (Real.exp (120 * Real.exp 3)), ?_⟩
  intro X hX d p q r k n' hMt hC _
  have hXa : X₁ ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hXb : (2 : ℝ) ^ 15 ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hXe : Real.exp (120 * Real.exp 3) ≤ X := le_trans (le_max_right _ _) hX
  obtain ⟨_, _, hreg⟩ := hX₁ X hXa
  obtain ⟨hlogY1, hlogY3, hl2, hlX, hl3⟩ := SvSmallH.logY_facts hXe
  obtain ⟨_, p₁, p₁', hN1, hN2, hcol⟩ := hC
  obtain ⟨hp₁, hn1, hnp₁, hRn, _⟩ := SvSmallH.nPart_facts hXb hreg hN1
  obtain ⟨hp₂, hn1', hnp₂, hRn', _⟩ := SvSmallH.nPart_facts hXb hreg hN2
  have E := SvSmallH.collision_eq hp₁ hnp₁ hn1 hp₂ hnp₂ hn1' hcol
  obtain ⟨_, _, _, hda, _, _, _, _⟩ := SvSmallH.regAt_basic hn1 hRn
  obtain ⟨_, _, _, hda', _, _, _, _⟩ := SvSmallH.regAt_basic hn1' hRn'
  have hdg : d ∣ SV.gcdS (q * r * k) n' := Nat.dvd_gcd hda hda'
  have hhg : SV.gcdS (q * r * k) n' / d ∣ SV.gcdS (q * r * k) n' := Nat.div_dvd_of_dvd hdg
  have hgdiff : (SV.gcdS (q * r * k) n' : ℤ) ∣ (sig (q * r * k) : ℤ) - (sig n' : ℤ) := by
    have e : (sig (q * r * k) : ℤ) - (sig n' : ℤ) =
        (p₁' : ℤ) * aliquot n' - (p₁ : ℤ) * aliquot (q * r * k) := by linarith
    rw [e]
    exact dvd_sub (dvd_mul_of_dvd_right (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right _ _)) _)
      (dvd_mul_of_dvd_right (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left _ _)) _)
  have hgabs : SV.gcdS (q * r * k) n' ∣ ((sig (q * r * k) : ℤ) - (sig n' : ℤ)).natAbs :=
    Int.natCast_dvd.mp hgdiff
  -- the thresholds `a = (log log X)^2 ≤ b = log X`
  have ha2 : (2 : ℝ) ≤ (logIt 2 X) ^ 2 := by nlinarith
  have hab : (logIt 2 X) ^ 2 ≤ Real.log X := SvSmallH.log_sq_le (by linarith)
  have hmert := hK _ _ ha2 hab
  have hloga : Real.log ((logIt 2 X) ^ 2) = 2 * logIt 3 X := by
    rw [Real.log_pow]
    push_cast
    rfl
  have hl3pos : 0 < logIt 3 X := by linarith
  have hl2pos : 0 < logIt 2 X := by linarith
  -- the big bound `e^{S₀+4} ≤ L`
  set L : ℝ := Real.exp (K + 4) / 2 * (logIt 2 X / Real.log (SV.Ycut X)) with hL
  have hBig : Real.exp (Real.log (Real.log (Real.log X)) - Real.log (Real.log ((logIt 2 X) ^ 2)) +
      K / Real.log ((logIt 2 X) ^ 2) + 4) ≤ L := by
    rw [hloga]
    have hKa : K / (2 * logIt 3 X) ≤ K := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    have e1 : Real.log (Real.log (Real.log X)) = Real.log (logIt 2 X) := rfl
    rw [e1]
    have e2 : Real.log (logIt 2 X) - Real.log (2 * logIt 3 X) + K / (2 * logIt 3 X) + 4 =
        (Real.log (logIt 2 X) - Real.log (2 * logIt 3 X)) + (K / (2 * logIt 3 X) + 4) := by ring
    rw [e2, Real.exp_add, Real.exp_sub, Real.exp_log hl2pos, Real.exp_log (by linarith)]
    have h3 : Real.exp (K / (2 * logIt 3 X) + 4) ≤ Real.exp (K + 4) :=
      Real.exp_le_exp.mpr (by linarith)
    have h4 : logIt 2 X / (2 * logIt 3 X) ≤ logIt 2 X / Real.log (SV.Ycut X) / 2 := by
      rw [div_div]
      apply div_le_div_of_nonneg_left hl2pos.le (by linarith) (by linarith)
    have h5 : 0 ≤ logIt 2 X / (2 * logIt 3 X) := by positivity
    calc logIt 2 X / (2 * logIt 3 X) * Real.exp (K / (2 * logIt 3 X) + 4)
        ≤ logIt 2 X / Real.log (SV.Ycut X) / 2 * Real.exp (K + 4) :=
          mul_le_mul h4 h3 (Real.exp_pos _).le (by positivity)
      _ = L := by rw [hL]; ring
  -- the index sets
  unfold SV.ratio322 SV.frak
  set I := (SV.A3 (q * r * k) n').primeFactors.filter
      (fun p : ℕ => (logIt 2 X) ^ 2 < (p : ℝ) ∧ (p : ℝ) ≤ Real.log X ∧ ¬ p ∣ sig (q * r * k) ∧
        ¬ p ∣ aliquot n') with hI
  set P := SV.primesIoc ((logIt 2 X) ^ 2) (Real.log X) with hP
  set J := P.filter (fun q₀ : ℕ => (q₀ : ℤ) ∣ (sig (q * r * k) : ℤ) - (sig n' : ℤ) ∧
      ¬ q₀ ∣ SV.gcdS (q * r * k) n' / d * sig (q * r * k)) with hJ
  have hIP : I ⊆ P := by
    intro p hp
    rw [hI, Finset.mem_filter] at hp
    rw [hP, SV.primesIoc, Finset.mem_filter, Finset.mem_Iic]
    exact ⟨Nat.le_floor hp.2.2.1, Nat.prime_of_mem_primeFactors hp.1, hp.2.1⟩
  have hIJ : I ⊆ J := by
    intro p hp
    have hpP := hIP hp
    rw [hI, Finset.mem_filter] at hp
    obtain ⟨hpf, _, _, hns, hna⟩ := hp
    have hpp := Nat.prime_of_mem_primeFactors hpf
    rw [hJ, Finset.mem_filter]
    refine ⟨hpP, ?_, ?_⟩
    · apply Int.natCast_dvd.mpr
      exact dvd_trans (Nat.dvd_of_mem_primeFactors hpf) (Nat.div_dvd_of_dvd hgabs)
    · intro hdiv
      rcases (Nat.Prime.dvd_mul hpp).mp hdiv with h1 | h1
      · exact hna (dvd_trans h1 (dvd_trans hhg (Nat.gcd_dvd_right _ _)))
      · exact hns h1
  have hP2 : ∀ p ∈ P, 2 ≤ p := by
    intro p hp
    rw [hP, SV.primesIoc, Finset.mem_filter] at hp
    exact hp.2.1.two_le
  have core := SvSmallH.totient_core I P J hIP hIJ hP2 hmert hBig
  refine le_trans core ?_
  have hJ0 : 0 ≤ ∑ p ∈ J, (1 : ℝ) / p := Finset.sum_nonneg (fun p _ => by positivity)
  have hq : 0 ≤ logIt 2 X / Real.log (SV.Ycut X) := by positivity
  have hm1 : 1 ≤ max 1 (Real.exp (K + 4) / 2) := le_max_left _ _
  have hm2 : Real.exp (K + 4) / 2 ≤ max 1 (Real.exp (K + 4) / 2) := le_max_right _ _
  have he2 : 0 < Real.exp 2 := Real.exp_pos 2
  have key : 1 + L * ∑ p ∈ J, (1 : ℝ) / p ≤
      max 1 (Real.exp (K + 4) / 2) * (1 + logIt 2 X / Real.log (SV.Ycut X) * ∑ p ∈ J, (1 : ℝ) / p) := by
    rw [hL]
    have h6 : 0 ≤ logIt 2 X / Real.log (SV.Ycut X) * ∑ p ∈ J, (1 : ℝ) / p := mul_nonneg hq hJ0
    nlinarith
  calc Real.exp 2 * (1 + L * ∑ p ∈ J, (1 : ℝ) / p)
      ≤ Real.exp 2 * (max 1 (Real.exp (K + 4) / 2) *
          (1 + logIt 2 X / Real.log (SV.Ycut X) * ∑ p ∈ J, (1 : ℝ) / p)) :=
        mul_le_mul_of_nonneg_left key he2.le
    _ = Real.exp 2 * max 1 (Real.exp (K + 4) / 2) *
          (1 + logIt 2 X / Real.log (SV.Ycut X) * ∑ p ∈ J, (1 : ℝ) / p) := by ring

end Principia.Erdos1054.Proofs

namespace Principia.Erdos1054.Proofs.SvSmallH

open Finset

/-! ## Brun–Titchmarsh reciprocal sums over progressions -/

/-- `Std_BrunTitchmarsh` with a given constant. -/
def BTbound (C : ℝ) : Prop :=
  ∀ m a : ℕ, 1 ≤ m → Nat.Coprime a m → ∀ x : ℝ, (m : ℝ) < x →
    (piAP x m a : ℝ) ≤ C * x / ((m.totient : ℝ) * Real.log (x / m))

/-- The Brun–Titchmarsh constant may be taken nonnegative. -/
lemma BT_nonneg (h : Std_BrunTitchmarsh) : ∃ C : ℝ, 0 ≤ C ∧ BTbound C := by
  obtain ⟨C, hC⟩ := h
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro m a hm ha x hx
  refine le_trans (hC m a hm ha x hx) ?_
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hx0 : 0 ≤ x := le_trans hm0.le hx.le
  have hφ : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hlog : 0 < Real.log (x / m) := Real.log_pos ((one_lt_div hm0).mpr hx)
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact mul_le_mul_of_nonneg_right (le_max_left _ _) hx0

/-- One dyadic block: `∑_{U2^j < p ≤ U2^{j+1}, p ≡ a (m)} 1/p ≤ 2C/(φ(m) log T)` when `mT ≤ U`. -/
lemma BT_block {C : ℝ} (hC0 : 0 ≤ C) (hBT : BTbound C) {m a : ℕ} (hm : 1 ≤ m)
    (ha : Nat.Coprime a m) {U T : ℝ} (hT : 1 < T) (hmT : (m : ℝ) * T ≤ U) (j : ℕ) :
    ∑ p ∈ (SV.primesIoc (U * 2 ^ j) (U * 2 ^ (j + 1))).filter (fun p => p ≡ a [MOD m]),
      (1 : ℝ) / p ≤ 2 * C / ((m.totient : ℝ) * Real.log T) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hU : (m : ℝ) < U := by nlinarith
  have hU0 : 0 < U := by linarith
  have h2j : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  have hx : (m : ℝ) < U * 2 ^ (j + 1) := by
    have : U ≤ U * 2 ^ (j + 1) := le_mul_of_one_le_right hU0.le (one_le_pow₀ (by norm_num))
    linarith
  have hφ : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hlogT : 0 < Real.log T := Real.log_pos hT
  have hlog : Real.log T ≤ Real.log (U * 2 ^ (j + 1) / m) := by
    apply Real.log_le_log (by linarith)
    rw [le_div_iff₀ hm0]
    have : U ≤ U * 2 ^ (j + 1) := le_mul_of_one_le_right hU0.le (one_le_pow₀ (by norm_num))
    nlinarith
  have hcard : ((SV.primesIoc (U * 2 ^ j) (U * 2 ^ (j + 1))).filter
      (fun p => p ≡ a [MOD m])).card ≤ piAP (U * 2 ^ (j + 1)) m a := by
    unfold piAP
    apply Finset.card_le_card
    intro p hp
    unfold SV.primesIoc at hp
    rw [Finset.mem_filter, Finset.mem_filter] at hp
    rw [Finset.mem_filter]
    exact ⟨hp.1.1, hp.1.2.1, hp.2⟩
  have hterm : ∀ p ∈ (SV.primesIoc (U * 2 ^ j) (U * 2 ^ (j + 1))).filter
      (fun p => p ≡ a [MOD m]), (1 : ℝ) / p ≤ 1 / (U * 2 ^ j) := by
    intro p hp
    unfold SV.primesIoc at hp
    rw [Finset.mem_filter, Finset.mem_filter] at hp
    exact one_div_le_one_div_of_le (by positivity) hp.1.2.2.le
  have hBTx := hBT m a hm ha _ hx
  calc ∑ p ∈ (SV.primesIoc (U * 2 ^ j) (U * 2 ^ (j + 1))).filter (fun p => p ≡ a [MOD m]),
        (1 : ℝ) / p
      ≤ ∑ p ∈ (SV.primesIoc (U * 2 ^ j) (U * 2 ^ (j + 1))).filter (fun p => p ≡ a [MOD m]),
          (1 : ℝ) / (U * 2 ^ j) := Finset.sum_le_sum hterm
    _ = (((SV.primesIoc (U * 2 ^ j) (U * 2 ^ (j + 1))).filter
          (fun p => p ≡ a [MOD m])).card : ℝ) * (1 / (U * 2 ^ j)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (piAP (U * 2 ^ (j + 1)) m a : ℝ) * (1 / (U * 2 ^ j)) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
    _ ≤ C * (U * 2 ^ (j + 1)) / ((m.totient : ℝ) * Real.log (U * 2 ^ (j + 1) / m)) *
          (1 / (U * 2 ^ j)) := mul_le_mul_of_nonneg_right hBTx (by positivity)
    _ ≤ C * (U * 2 ^ (j + 1)) / ((m.totient : ℝ) * Real.log T) * (1 / (U * 2 ^ j)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_left hlog hφ.le
    _ = 2 * C / ((m.totient : ℝ) * Real.log T) := by
        rw [pow_succ]
        field_simp

/-- `J` dyadic blocks: `∑_{U < p ≤ U2^J, p ≡ a (m)} 1/p ≤ J · 2C/(φ(m) log T)`. -/
lemma BT_dyadic {C : ℝ} (hC0 : 0 ≤ C) (hBT : BTbound C) {m a : ℕ} (hm : 1 ≤ m)
    (ha : Nat.Coprime a m) {U T : ℝ} (hT : 1 < T) (hmT : (m : ℝ) * T ≤ U) (J : ℕ) :
    ∑ p ∈ (SV.primesIoc U (U * 2 ^ J)).filter (fun p => p ≡ a [MOD m]), (1 : ℝ) / p ≤
      J * (2 * C / ((m.totient : ℝ) * Real.log T)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hU0 : 0 < U := by nlinarith
  induction J with
  | zero =>
    have hE : (SV.primesIoc U (U * 2 ^ 0)).filter (fun p => p ≡ a [MOD m]) = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro p hp
      unfold SV.primesIoc at hp
      rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_Iic, pow_zero, mul_one] at hp
      have h1 : (p : ℝ) ≤ U := le_trans (Nat.cast_le.mpr hp.1.1) (Nat.floor_le hU0.le)
      linarith [hp.1.2.2]
    rw [hE, Finset.sum_empty]
    simp
  | succ J ih =>
    have hsub : (SV.primesIoc U (U * 2 ^ (J + 1))).filter (fun p => p ≡ a [MOD m]) ⊆
        (SV.primesIoc U (U * 2 ^ J)).filter (fun p => p ≡ a [MOD m]) ∪
          (SV.primesIoc (U * 2 ^ J) (U * 2 ^ (J + 1))).filter (fun p => p ≡ a [MOD m]) := by
      intro p hp
      unfold SV.primesIoc at hp
      rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_Iic] at hp
      rw [Finset.mem_union]
      by_cases hcase : (p : ℝ) ≤ U * 2 ^ J
      · left
        unfold SV.primesIoc
        rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_Iic]
        exact ⟨⟨Nat.le_floor hcase, hp.1.2.1, hp.1.2.2⟩, hp.2⟩
      · right
        unfold SV.primesIoc
        rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_Iic]
        exact ⟨⟨hp.1.1, hp.1.2.1, lt_of_not_ge hcase⟩, hp.2⟩
    have hblock := BT_block hC0 hBT hm ha hT hmT J
    have hnn : ∀ p ∈ (SV.primesIoc U (U * 2 ^ J)).filter (fun p => p ≡ a [MOD m]) ∪
        (SV.primesIoc (U * 2 ^ J) (U * 2 ^ (J + 1))).filter (fun p => p ≡ a [MOD m]),
        (0 : ℝ) ≤ 1 / p := fun p _ => by positivity
    have hinter := Finset.sum_union_inter (s₁ := (SV.primesIoc U (U * 2 ^ J)).filter
      (fun p => p ≡ a [MOD m])) (s₂ := (SV.primesIoc (U * 2 ^ J) (U * 2 ^ (J + 1))).filter
      (fun p => p ≡ a [MOD m])) (f := fun p : ℕ => (1 : ℝ) / p)
    have hi0 : 0 ≤ ∑ p ∈ (SV.primesIoc U (U * 2 ^ J)).filter (fun p => p ≡ a [MOD m]) ∩
        (SV.primesIoc (U * 2 ^ J) (U * 2 ^ (J + 1))).filter (fun p => p ≡ a [MOD m]),
        (1 : ℝ) / p := Finset.sum_nonneg (fun p _ => by positivity)
    calc ∑ p ∈ (SV.primesIoc U (U * 2 ^ (J + 1))).filter (fun p => p ≡ a [MOD m]), (1 : ℝ) / p
        ≤ ∑ p ∈ (SV.primesIoc U (U * 2 ^ J)).filter (fun p => p ≡ a [MOD m]) ∪
            (SV.primesIoc (U * 2 ^ J) (U * 2 ^ (J + 1))).filter (fun p => p ≡ a [MOD m]),
            (1 : ℝ) / p := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p hp _ => hnn p hp)
      _ ≤ J * (2 * C / ((m.totient : ℝ) * Real.log T)) +
            2 * C / ((m.totient : ℝ) * Real.log T) := by linarith
      _ = ((J + 1 : ℕ) : ℝ) * (2 * C / ((m.totient : ℝ) * Real.log T)) := by
          push_cast
          ring

/-- **Reciprocal prime sum in one class.** If every element of `S` is a prime in `(U, V]`, the
elements are pairwise congruent modulo `m`, `mT ≤ U` and `V ≤ U 2^J`, then
`∑_{p ∈ S} 1/p ≤ J · 2C/(φ(m) log T)`. (If `S` is nonempty its class is that of a prime `> m`,
hence reduced.) -/
lemma class_recip {C : ℝ} (hC0 : 0 ≤ C) (hBT : BTbound C) {m : ℕ} (hm : 1 ≤ m)
    {U V T : ℝ} (hT : 1 < T) (hmT : (m : ℝ) * T ≤ U) (J : ℕ) (hVJ : V ≤ U * 2 ^ J)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p ∈ SV.primesIoc U V)
    (hcong : ∀ p ∈ S, ∀ p' ∈ S, p ≡ p' [MOD m]) :
    ∑ p ∈ S, (1 : ℝ) / p ≤ J * (2 * C / ((m.totient : ℝ) * Real.log T)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hU : (m : ℝ) < U := by nlinarith
  have hφ : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hlogT : 0 < Real.log T := Real.log_pos hT
  rcases S.eq_empty_or_nonempty with hE | ⟨p₀, hp₀⟩
  · rw [hE, Finset.sum_empty]
    positivity
  have hp₀' := hS p₀ hp₀
  unfold SV.primesIoc at hp₀'
  rw [Finset.mem_filter] at hp₀'
  have hcop : Nat.Coprime p₀ m := by
    apply (Nat.Prime.coprime_iff_not_dvd hp₀'.2.1).mpr
    intro hdvd
    have := Nat.le_of_dvd (by omega) hdvd
    have h2 : (p₀ : ℝ) ≤ m := by exact_mod_cast this
    linarith [hp₀'.2.2]
  have hsub : S ⊆ (SV.primesIoc U (U * 2 ^ J)).filter (fun p => p ≡ p₀ [MOD m]) := by
    intro p hp
    have hpS := hS p hp
    unfold SV.primesIoc at hpS ⊢
    rw [Finset.mem_filter, Finset.mem_Iic] at hpS
    rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_Iic]
    exact ⟨⟨le_trans hpS.1 (Nat.floor_mono hVJ), hpS.2⟩, hcong p hp p₀ hp₀⟩
  calc ∑ p ∈ S, (1 : ℝ) / p
      ≤ ∑ p ∈ (SV.primesIoc U (U * 2 ^ J)).filter (fun p => p ≡ p₀ [MOD m]), (1 : ℝ) / p :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)
    _ ≤ J * (2 * C / ((m.totient : ℝ) * Real.log T)) := BT_dyadic hC0 hBT hm hcop hT hmT J

/-- **Reciprocal sum over a sparse progression** (the trivial count used for `h > X^{1/20}`): if
the elements of `R` lie in `(U, V]` and are pairwise congruent modulo `h ≥ 1`, then
`∑_{r ∈ R} 1/r ≤ 1/U + (1 + log V)/h`. -/
lemma ap_recip_le (R : Finset ℕ) {h : ℕ} (hh : 1 ≤ h) {U V : ℝ} (hU : 0 < U) (hV : 1 ≤ V)
    (hR : ∀ r ∈ R, U < r ∧ (r : ℝ) ≤ V) (hcong : ∀ r ∈ R, ∀ r' ∈ R, r ≡ r' [MOD h]) :
    ∑ r ∈ R, (1 : ℝ) / r ≤ 1 / U + (1 + Real.log V) / h := by
  rw [← Finset.sum_filter_add_sum_filter_not R (fun r => r / h = 0)]
  have hh0 : (0 : ℝ) < h := by exact_mod_cast hh
  apply add_le_add
  · rcases (R.filter (fun r => r / h = 0)).eq_empty_or_nonempty with hE | ⟨r₀, hr₀⟩
    · rw [hE, Finset.sum_empty]
      positivity
    have hlt : ∀ r ∈ R.filter (fun r => r / h = 0), r < h := by
      intro r hr
      rw [Finset.mem_filter] at hr
      have e := Nat.div_add_mod r h
      rw [hr.2, mul_zero, zero_add] at e
      have := Nat.mod_lt r (show h > 0 by omega)
      omega
    have hsub : R.filter (fun r => r / h = 0) ⊆ {r₀} := by
      intro r hr
      rw [Finset.mem_singleton]
      have h1 := hlt r hr
      have h2 := hlt r₀ hr₀
      have hc := hcong r (Finset.mem_filter.mp hr).1 r₀ (Finset.mem_filter.mp hr₀).1
      unfold Nat.ModEq at hc
      rwa [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at hc
    have hr0U := (hR r₀ (Finset.mem_filter.mp hr₀).1).1
    calc ∑ r ∈ R.filter (fun r => r / h = 0), (1 : ℝ) / r ≤ ∑ r ∈ ({r₀} : Finset ℕ), (1 : ℝ) / r :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ = 1 / (r₀ : ℝ) := Finset.sum_singleton _ _
      _ ≤ 1 / U := one_div_le_one_div_of_le hU hr0U.le
  · have hinj : Set.InjOn (fun r => r / h) (R.filter (fun r => ¬ r / h = 0) : Set ℕ) := by
      intro r hr r' hr' heq
      rw [Finset.mem_coe, Finset.mem_filter] at hr hr'
      have hc := hcong r hr.1 r' hr'.1
      unfold Nat.ModEq at hc
      simp only at heq
      rw [← Nat.div_add_mod r h, ← Nat.div_add_mod r' h, heq, hc]
    calc ∑ r ∈ R.filter (fun r => ¬ r / h = 0), (1 : ℝ) / r
        ≤ ∑ r ∈ R.filter (fun r => ¬ r / h = 0), (1 : ℝ) / ((h : ℝ) * ((r / h : ℕ) : ℝ)) := by
          apply Finset.sum_le_sum
          intro r hr
          have hi : 1 ≤ r / h := Nat.one_le_iff_ne_zero.mpr (Finset.mem_filter.mp hr).2
          have hi' : (1 : ℝ) ≤ ((r / h : ℕ) : ℝ) := by exact_mod_cast hi
          apply one_div_le_one_div_of_le (by positivity)
          have : h * (r / h) ≤ r := Nat.mul_div_le r h
          exact_mod_cast this
      _ = ∑ i ∈ (R.filter (fun r => ¬ r / h = 0)).image (fun r => r / h),
            (1 : ℝ) / ((h : ℝ) * (i : ℝ)) :=
            (Finset.sum_image (f := fun i : ℕ => (1 : ℝ) / ((h : ℝ) * (i : ℝ))) hinj).symm
      _ ≤ ∑ i ∈ Finset.Icc 1 ⌊V⌋₊, (1 : ℝ) / ((h : ℝ) * (i : ℝ)) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro i hi
            rw [Finset.mem_image] at hi
            obtain ⟨r, hr, rfl⟩ := hi
            rw [Finset.mem_Icc]
            have hrm := Finset.mem_filter.mp hr
            refine ⟨Nat.one_le_iff_ne_zero.mpr hrm.2, ?_⟩
            exact le_trans (Nat.div_le_self r h) (Nat.le_floor (hR r hrm.1).2)
          · intro i _ _
            positivity
      _ = (1 / (h : ℝ)) * ∑ i ∈ Finset.Icc 1 ⌊V⌋₊, ((i : ℕ) : ℝ)⁻¹ := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
      _ ≤ (1 / (h : ℝ)) * (1 + Real.log V) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have h1 := harmonic_le_one_add_log ⌊V⌋₊
          simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at h1
          have h2 : Real.log (⌊V⌋₊ : ℝ) ≤ Real.log V := by
            rcases Nat.eq_zero_or_pos ⌊V⌋₊ with h0 | h0
            · rw [h0, Nat.cast_zero, Real.log_zero]
              exact Real.log_nonneg hV
            · exact Real.log_le_log (by exact_mod_cast h0) (Nat.floor_le (by linarith))
          linarith
      _ = (1 + Real.log V) / h := by ring

end Principia.Erdos1054.Proofs.SvSmallH

namespace Principia.Erdos1054.Proofs.SvSmallH

open Finset

/-! ## Sizes for large `X` -/

/-- The threshold facts used by the progression estimates, for `X ≥ exp(120 e^3)`. -/
lemma bigX_facts {X : ℝ} (hX : Real.exp (120 * Real.exp 3) ≤ X) :
    1 < X ∧ 480 ≤ Real.log X ∧ Real.log X ≤ X ^ ((1 : ℝ) / 30) ∧
      X ^ ((1 : ℝ) / 60) ≤ 2 ^ ⌈Real.log X⌉₊ ∧ (⌈Real.log X⌉₊ : ℝ) ≤ 2 * Real.log X ∧
      (2 : ℝ) ^ 15 ≤ X := by
  obtain ⟨_, _, _, hlX, _⟩ := logY_facts hX
  have hX0 : 0 < X := lt_of_lt_of_le (Real.exp_pos _) hX
  have hX1 : 1 < X := by
    rw [← Real.log_pos_iff hX0.le]
    linarith
  have he1 : (2.7 : ℝ) < Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
  -- `X^{1/60} ≥ e^8 ≥ 60`
  have h60 : (60 : ℝ) ≤ X ^ ((1 : ℝ) / 60) := by
    rw [Real.rpow_def_of_pos hX0]
    have h8 : (8 : ℝ) ≤ Real.log X * (1 / 60) := by linarith
    have he8 : Real.exp 8 = Real.exp 1 ^ 8 := by rw [← Real.exp_nat_mul]; norm_num
    have : (60 : ℝ) ≤ Real.exp 8 := by
      rw [he8]
      have : (2.7 : ℝ) ^ 8 ≤ Real.exp 1 ^ 8 := pow_le_pow_left₀ (by norm_num) he1.le 8
      linarith [show (60 : ℝ) ≤ 2.7 ^ 8 by norm_num]
    exact le_trans this (Real.exp_le_exp.mpr h8)
  have hlog30 : Real.log X ≤ X ^ ((1 : ℝ) / 30) := by
    have h1 : Real.log X ≤ X ^ ((1 : ℝ) / 60) / (1 / 60) := Real.log_le_rpow_div hX0.le (by norm_num)
    have e : X ^ ((1 : ℝ) / 30) = X ^ ((1 : ℝ) / 60) * X ^ ((1 : ℝ) / 60) := by
      rw [← Real.rpow_add hX0]
      norm_num
    rw [e]
    have hp : 0 ≤ X ^ ((1 : ℝ) / 60) := Real.rpow_nonneg hX0.le _
    have : X ^ ((1 : ℝ) / 60) / (1 / 60) = 60 * X ^ ((1 : ℝ) / 60) := by ring
    rw [this] at h1
    nlinarith
  have hJ : Real.log X ≤ (⌈Real.log X⌉₊ : ℝ) := Nat.le_ceil _
  have hJ2 : (⌈Real.log X⌉₊ : ℝ) ≤ 2 * Real.log X := by
    have := Nat.ceil_lt_add_one (show 0 ≤ Real.log X by linarith)
    linarith
  have h2J : X ^ ((1 : ℝ) / 60) ≤ 2 ^ ⌈Real.log X⌉₊ := by
    rw [← Real.log_le_log_iff (by positivity) (by positivity), Real.log_rpow hX0, Real.log_pow]
    have hl2 := Real.log_two_gt_d9
    nlinarith
  have h215 : (2 : ℝ) ^ 15 ≤ X := by
    have h1 : (2 : ℝ) ^ 15 ≤ Real.exp 1 ^ 15 := pow_le_pow_left₀ (by norm_num) (by linarith) 15
    have h2 : Real.exp 1 ^ 15 = Real.exp 15 := by rw [← Real.exp_nat_mul]; norm_num
    have h3 : Real.exp 15 ≤ Real.exp (120 * Real.exp 3) := by
      apply Real.exp_le_exp.mpr
      have := Real.add_one_le_exp (3 : ℝ)
      linarith
    linarith
  exact ⟨hX1, hlX, hlog30, h2J, hJ2, h215⟩

/-- The range facts of `k ∈ SV.kSet X d`, `q ∈ SV.qClass X h a`, `r ∈ SV.rClass X h b`. -/
lemma qr_facts {X : ℝ} (hX1 : 1 < X) {d h a b k q r : ℕ} (hk : k ∈ SV.kSet X d)
    (hq : q ∈ SV.qClass X h a) (hr : r ∈ SV.rClass X h b) :
    q.Prime ∧ r.Prime ∧ 1 ≤ k ∧ k < r ∧ r * k < q ∧ X ^ ((7 : ℝ) / 20) < q ∧
      (q : ℝ) ≤ X ^ ((11 : ℝ) / 30) ∧ X ^ ((1 : ℝ) / 15) < r ∧ (r : ℝ) ≤ X ^ ((1 : ℝ) / 12) ∧
      q ≡ a [MOD h] ∧ r ≡ b [MOD h] := by
  have hX0 : 0 < X := by linarith
  unfold SV.kSet at hk
  unfold SV.qClass SV.primesIoc at hq
  unfold SV.rClass SV.primesIoc at hr
  rw [Finset.mem_filter, Finset.mem_Iic] at hk
  rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_Iic] at hq hr
  have hk1 : (0 : ℝ) < k := lt_of_le_of_lt (Real.rpow_nonneg hX0.le _) hk.2.1
  have hk2 : (k : ℝ) ≤ X ^ ((1 : ℝ) / 60) :=
    le_trans (Nat.cast_le.mpr hk.1) (Nat.floor_le (Real.rpow_nonneg hX0.le _))
  have hq2 : (q : ℝ) ≤ X ^ ((11 : ℝ) / 30) :=
    le_trans (Nat.cast_le.mpr hq.1.1) (Nat.floor_le (Real.rpow_nonneg hX0.le _))
  have hr2 : (r : ℝ) ≤ X ^ ((1 : ℝ) / 12) :=
    le_trans (Nat.cast_le.mpr hr.1.1) (Nat.floor_le (Real.rpow_nonneg hX0.le _))
  have hkr : (k : ℝ) < r := by
    calc (k : ℝ) ≤ X ^ ((1 : ℝ) / 60) := hk2
      _ < X ^ ((1 : ℝ) / 15) := rpow_lt_of_lt hX1 (by norm_num)
      _ < r := hr.1.2.2
  have hrk : (r : ℝ) * k < q := by
    calc (r : ℝ) * k ≤ X ^ ((1 : ℝ) / 12) * X ^ ((1 : ℝ) / 60) :=
          mul_le_mul hr2 hk2 hk1.le (Real.rpow_nonneg hX0.le _)
      _ = X ^ ((1 : ℝ) / 12 + 1 / 60) := (Real.rpow_add hX0 _ _).symm
      _ < X ^ ((7 : ℝ) / 20) := rpow_lt_of_lt hX1 (by norm_num)
      _ < q := hq.1.2.2
  refine ⟨hq.1.2.1, hr.1.2.1, ?_, ?_, ?_, hq.1.2.2, hq2, hr.1.2.2, hr2, hq.2, hr.2⟩
  · exact_mod_cast hk1
  · exact_mod_cast hkr
  · exact_mod_cast hrk

/-- `1/φ(h) ≤ K/h` from `h/φ(h) ≤ K` (`eq:sv-totient` with `eq:sv-image-abundancy`). -/
lemma inv_totient_le (htot : Eq_SvTotient) {B : ℝ} {h m : ℕ} (hh : 1 ≤ h) (hm : 1 ≤ m)
    (hhm : h ∣ m) (hB : abundancy m ≤ B) :
    (1 : ℝ) / (h.totient : ℝ) ≤ Real.pi ^ 2 / 6 * B / h := by
  obtain ⟨t1, t2⟩ := htot h m hh hm hhm
  have hh0 : (0 : ℝ) < h := by exact_mod_cast hh
  have hφ : (0 : ℝ) < h.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have h1 : (h : ℝ) / (h.totient : ℝ) ≤ Real.pi ^ 2 / 6 * B :=
    le_trans t1 (mul_le_mul_of_nonneg_left (le_trans t2 hB) (by positivity))
  rw [div_le_div_iff₀ hφ hh0]
  rw [div_le_iff₀ hφ] at h1
  linarith


/-! ## The progression sums of `eq:sv-f-sum` and `eq:sv-qr-sum` -/

/-- **`q` in one class**: `∑_{q ∈ S} 1/q ≤ 400 C/φ(m)` for primes `q ∈ (X^{7/20}, X^{11/30}]`
pairwise congruent modulo `m`, when `m X^{1/100} ≤ X^{7/20}` (Brun–Titchmarsh, `T = X^{1/100}`). -/
lemma q_class_sum {C : ℝ} (hC0 : 0 ≤ C) (hBT : BTbound C) {X : ℝ}
    (hXe : Real.exp (120 * Real.exp 3) ≤ X) {m : ℕ} (hm : 1 ≤ m)
    (hmT : (m : ℝ) * X ^ ((1 : ℝ) / 100) ≤ X ^ ((7 : ℝ) / 20)) (S : Finset ℕ)
    (hS : ∀ q ∈ S, q ∈ SV.primesIoc (X ^ ((7 : ℝ) / 20)) (X ^ ((11 : ℝ) / 30)))
    (hcong : ∀ q ∈ S, ∀ q' ∈ S, q ≡ q' [MOD m]) :
    ∑ q ∈ S, (1 : ℝ) / q ≤ 400 * C / (m.totient : ℝ) := by
  obtain ⟨hX1, hlX, _, h2J, hJ2, _⟩ := bigX_facts hXe
  have hX0 : 0 < X := by linarith
  have hT : (1 : ℝ) < X ^ ((1 : ℝ) / 100) := Real.one_lt_rpow hX1 (by norm_num)
  have hVJ : X ^ ((11 : ℝ) / 30) ≤ X ^ ((7 : ℝ) / 20) * 2 ^ ⌈Real.log X⌉₊ := by
    have e : X ^ ((11 : ℝ) / 30) = X ^ ((7 : ℝ) / 20) * X ^ ((1 : ℝ) / 60) := by
      rw [← Real.rpow_add hX0]
      norm_num
    rw [e]
    exact mul_le_mul_of_nonneg_left h2J (Real.rpow_nonneg hX0.le _)
  have hcr := class_recip hC0 hBT hm hT hmT ⌈Real.log X⌉₊ hVJ S hS hcong
  have hlogT : Real.log (X ^ ((1 : ℝ) / 100)) = Real.log X / 100 := by
    rw [Real.log_rpow hX0]
    ring
  have hφ : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hlX0 : 0 < Real.log X := by linarith
  rw [hlogT] at hcr
  have e1 : (⌈Real.log X⌉₊ : ℝ) * (2 * C / ((m.totient : ℝ) * (Real.log X / 100))) =
      (⌈Real.log X⌉₊ : ℝ) / Real.log X * (200 * C / (m.totient : ℝ)) := by
    field_simp
    ring
  have e2 : (⌈Real.log X⌉₊ : ℝ) / Real.log X ≤ 2 := by
    rw [div_le_iff₀ hlX0]
    linarith
  have h3 : 0 ≤ 200 * C / (m.totient : ℝ) := by positivity
  calc ∑ q ∈ S, (1 : ℝ) / q ≤ (⌈Real.log X⌉₊ : ℝ) / Real.log X * (200 * C / (m.totient : ℝ)) := by
        rw [← e1]
        exact hcr
    _ ≤ 2 * (200 * C / (m.totient : ℝ)) := mul_le_mul_of_nonneg_right e2 h3
    _ = 400 * C / (m.totient : ℝ) := by ring

/-- **`r` in one class, `m ≤ X^{1/20}`**: `∑_{r ∈ S} 1/r ≤ 240 C/φ(m)` for primes
`r ∈ (X^{1/15}, X^{1/12}]` pairwise congruent modulo `m`, when `m X^{1/60} ≤ X^{1/15}`. -/
lemma r_class_sum_small {C : ℝ} (hC0 : 0 ≤ C) (hBT : BTbound C) {X : ℝ}
    (hXe : Real.exp (120 * Real.exp 3) ≤ X) {m : ℕ} (hm : 1 ≤ m)
    (hmT : (m : ℝ) * X ^ ((1 : ℝ) / 60) ≤ X ^ ((1 : ℝ) / 15)) (S : Finset ℕ)
    (hS : ∀ r ∈ S, r ∈ SV.primesIoc (X ^ ((1 : ℝ) / 15)) (X ^ ((1 : ℝ) / 12)))
    (hcong : ∀ r ∈ S, ∀ r' ∈ S, r ≡ r' [MOD m]) :
    ∑ r ∈ S, (1 : ℝ) / r ≤ 240 * C / (m.totient : ℝ) := by
  obtain ⟨hX1, hlX, _, h2J, hJ2, _⟩ := bigX_facts hXe
  have hX0 : 0 < X := by linarith
  have hT : (1 : ℝ) < X ^ ((1 : ℝ) / 60) := Real.one_lt_rpow hX1 (by norm_num)
  have hVJ : X ^ ((1 : ℝ) / 12) ≤ X ^ ((1 : ℝ) / 15) * 2 ^ ⌈Real.log X⌉₊ := by
    have e : X ^ ((1 : ℝ) / 12) = X ^ ((1 : ℝ) / 15) * X ^ ((1 : ℝ) / 60) := by
      rw [← Real.rpow_add hX0]
      norm_num
    rw [e]
    exact mul_le_mul_of_nonneg_left h2J (Real.rpow_nonneg hX0.le _)
  have hcr := class_recip hC0 hBT hm hT hmT ⌈Real.log X⌉₊ hVJ S hS hcong
  have hlogT : Real.log (X ^ ((1 : ℝ) / 60)) = Real.log X / 60 := by
    rw [Real.log_rpow hX0]
    ring
  have hφ : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hlX0 : 0 < Real.log X := by linarith
  rw [hlogT] at hcr
  have e1 : (⌈Real.log X⌉₊ : ℝ) * (2 * C / ((m.totient : ℝ) * (Real.log X / 60))) =
      (⌈Real.log X⌉₊ : ℝ) / Real.log X * (120 * C / (m.totient : ℝ)) := by
    field_simp
    ring
  have e2 : (⌈Real.log X⌉₊ : ℝ) / Real.log X ≤ 2 := by
    rw [div_le_iff₀ hlX0]
    linarith
  have h3 : 0 ≤ 120 * C / (m.totient : ℝ) := by positivity
  calc ∑ r ∈ S, (1 : ℝ) / r ≤ (⌈Real.log X⌉₊ : ℝ) / Real.log X * (120 * C / (m.totient : ℝ)) := by
        rw [← e1]
        exact hcr
    _ ≤ 2 * (120 * C / (m.totient : ℝ)) := mul_le_mul_of_nonneg_right e2 h3
    _ = 240 * C / (m.totient : ℝ) := by ring

/-- **`r` in one class, `h > X^{1/20}`** (the trivial count, EP1054.tex line 1812):
`∑_{r ∈ S} 1/r ≤ 3 log X / X^{1/20}`. -/
lemma r_class_sum_big {X : ℝ} (hXe : Real.exp (120 * Real.exp 3) ≤ X) {h : ℕ} (hh1 : 1 ≤ h)
    (hbig : X ^ ((1 : ℝ) / 20) < (h : ℝ)) (S : Finset ℕ)
    (hS : ∀ r ∈ S, r ∈ SV.primesIoc (X ^ ((1 : ℝ) / 15)) (X ^ ((1 : ℝ) / 12)))
    (hcong : ∀ r ∈ S, ∀ r' ∈ S, r ≡ r' [MOD h]) :
    ∑ r ∈ S, (1 : ℝ) / r ≤ 3 * Real.log X / X ^ ((1 : ℝ) / 20) := by
  obtain ⟨hX1, hlX, _, _, _, _⟩ := bigX_facts hXe
  have hX0 : 0 < X := by linarith
  have hX20 : 0 < X ^ ((1 : ℝ) / 20) := Real.rpow_pos_of_pos hX0 _
  have hR : ∀ r ∈ S, X ^ ((1 : ℝ) / 15) < (r : ℝ) ∧ (r : ℝ) ≤ X ^ ((1 : ℝ) / 12) := by
    intro r hr
    have := hS r hr
    unfold SV.primesIoc at this
    rw [Finset.mem_filter, Finset.mem_Iic] at this
    exact ⟨this.2.2, le_trans (Nat.cast_le.mpr this.1) (Nat.floor_le (Real.rpow_nonneg hX0.le _))⟩
  have hV1 : (1 : ℝ) ≤ X ^ ((1 : ℝ) / 12) := Real.one_le_rpow hX1.le (by norm_num)
  have hap := ap_recip_le S hh1 (Real.rpow_pos_of_pos hX0 _) hV1 hR hcong
  have hlog12 : Real.log (X ^ ((1 : ℝ) / 12)) ≤ Real.log X := by
    rw [Real.log_rpow hX0]
    linarith
  have hlog12' : 0 ≤ Real.log (X ^ ((1 : ℝ) / 12)) := Real.log_nonneg hV1
  have h15 : 1 / X ^ ((1 : ℝ) / 15) ≤ 1 / X ^ ((1 : ℝ) / 20) :=
    one_div_le_one_div_of_le hX20 ((Real.rpow_le_rpow_left_iff hX1).mpr (by norm_num))
  have hhinv : 1 / (h : ℝ) ≤ 1 / X ^ ((1 : ℝ) / 20) := one_div_le_one_div_of_le hX20 hbig.le
  have h3 : 0 ≤ 1 / X ^ ((1 : ℝ) / 20) := by positivity
  calc ∑ r ∈ S, (1 : ℝ) / r
      ≤ 1 / X ^ ((1 : ℝ) / 15) + (1 + Real.log (X ^ ((1 : ℝ) / 12))) / h := hap
    _ = 1 / X ^ ((1 : ℝ) / 15) + (1 + Real.log (X ^ ((1 : ℝ) / 12))) * (1 / (h : ℝ)) := by ring
    _ ≤ 1 / X ^ ((1 : ℝ) / 20) + (1 + Real.log X) * (1 / X ^ ((1 : ℝ) / 20)) := by
        apply add_le_add h15
        exact mul_le_mul (by linarith) hhinv (by positivity) (by linarith)
    _ = (2 + Real.log X) * (1 / X ^ ((1 : ℝ) / 20)) := by ring
    _ ≤ (3 * Real.log X) * (1 / X ^ ((1 : ℝ) / 20)) :=
        mul_le_mul_of_nonneg_right (by linarith) h3
    _ = 3 * Real.log X / X ^ ((1 : ℝ) / 20) := by ring

/-- **The inner `q`-sum of `eq:sv-f-sum`** (EP1054.tex lines 1780–1806): for fixed `r` and a
prime `q₀` of `𝔣`, the admissible `q` lie in one class modulo `q₀h`, whence
`∑ 1/q ≤ 400C/φ(q₀h) ≤ (800 C K/h)/q₀` with `1/φ(h) ≤ K/h`. -/
lemma F_qpart {C : ℝ} (hC0 : 0 ≤ C) (hBT : BTbound C) {X : ℝ}
    (hXe : Real.exp (120 * Real.exp 3) ≤ X) {K : ℝ} (hK0 : 0 ≤ K) {d h a b k r q₀ n' : ℕ}
    (hh1 : 1 ≤ h) (hhX : (h : ℝ) ≤ X ^ ((10 : ℝ) / 33))
    (hphi_h : (1 : ℝ) / (h.totient : ℝ) ≤ K / h) (hk : k ∈ SV.kSet X d)
    (hr : r ∈ SV.rClass X h b) (hq₀ : q₀ ∈ SV.primesIoc ((logIt 2 X) ^ 2) (Real.log X)) :
    ∑ q ∈ (SV.qClass X h a).filter (fun q => (q₀ : ℤ) ∣ (sig (q * r * k) : ℤ) - (sig n' : ℤ) ∧
        ¬ q₀ ∣ h * sig (q * r * k)), (1 : ℝ) / q ≤ (800 * C * K / h) / q₀ := by
  obtain ⟨hX1, hlX, hlog30, _, _, _⟩ := bigX_facts hXe
  have hX0 : 0 < X := by linarith
  have hlX0 : 0 < Real.log X := by linarith
  have hh0 : (0 : ℝ) < h := by exact_mod_cast hh1
  have hq₀' := hq₀
  rw [SV.primesIoc, Finset.mem_filter, Finset.mem_Iic] at hq₀'
  have hq₀p : q₀.Prime := hq₀'.2.1
  have hq₀X : (q₀ : ℝ) ≤ Real.log X := le_trans (Nat.cast_le.mpr hq₀'.1) (Nat.floor_le hlX0.le)
  have hq₀2 : (2 : ℝ) ≤ q₀ := by exact_mod_cast hq₀p.two_le
  set S := (SV.qClass X h a).filter (fun q => (q₀ : ℤ) ∣ (sig (q * r * k) : ℤ) - (sig n' : ℤ) ∧
        ¬ q₀ ∣ h * sig (q * r * k)) with hS
  rcases S.eq_empty_or_nonempty with hE | ⟨q₁, hq₁⟩
  · rw [hE, Finset.sum_empty]
    positivity
  have hq₁' := hq₁
  rw [hS, Finset.mem_filter] at hq₁'
  have hq₀h : ¬ q₀ ∣ h := fun hd => hq₁'.2.2 (dvd_mul_of_dvd_left hd _)
  have hcop : Nat.Coprime q₀ h := (Nat.Prime.coprime_iff_not_dvd hq₀p).mpr hq₀h
  -- `σ(qrk) = (q+1)σ(rk)` on the class
  have hsig : ∀ q ∈ SV.qClass X h a, sig (q * r * k) = (q + 1) * sig (r * k) := by
    intro q hq
    obtain ⟨hqp, hrp, hk1, _, hrkq, _, _, _, _, _, _⟩ := qr_facts hX1 hk hq hr
    have hc : Nat.Coprime q (r * k) := (Nat.Prime.coprime_iff_not_dvd hqp).mpr (fun hd => by
      have := Nat.le_of_dvd (Nat.mul_pos hrp.pos hk1) hd
      omega)
    rw [mul_assoc, sig_mul hc, sig_prime hqp]
  have hq₀rk : ¬ q₀ ∣ sig (r * k) := by
    intro hd
    apply hq₁'.2.2
    rw [hsig q₁ hq₁'.1]
    exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right hd _) _
  -- pairwise congruent modulo `q₀ h`
  have hcong : ∀ q ∈ S, ∀ q' ∈ S, q ≡ q' [MOD q₀ * h] := by
    intro q hq q' hq'
    rw [hS, Finset.mem_filter] at hq hq'
    rw [← Nat.modEq_and_modEq_iff_modEq_mul hcop]
    constructor
    · rw [Nat.modEq_iff_dvd]
      have e1 := hq.2.1
      have e2 := hq'.2.1
      rw [hsig q hq.1] at e1
      rw [hsig q' hq'.1] at e2
      push_cast at e1 e2
      have h3 : (q₀ : ℤ) ∣ ((q' : ℤ) - q) * (sig (r * k) : ℤ) := by
        have e : ((q' : ℤ) - q) * (sig (r * k) : ℤ) =
            (((q' : ℤ) + 1) * (sig (r * k) : ℤ) - sig n') -
              (((q : ℤ) + 1) * (sig (r * k) : ℤ) - sig n') := by ring
        rw [e]
        exact dvd_sub e2 e1
      have hpz : Prime (q₀ : ℤ) := Nat.prime_iff_prime_int.mp hq₀p
      rcases hpz.dvd_or_dvd h3 with h4 | h4
      · exact h4
      · exact absurd (Int.natCast_dvd_natCast.mp h4) hq₀rk
    · obtain ⟨_, _, _, _, _, _, _, _, _, ha1, _⟩ := qr_facts hX1 hk hq.1 hr
      obtain ⟨_, _, _, _, _, _, _, _, _, ha2, _⟩ := qr_facts hX1 hk hq'.1 hr
      exact ha1.trans ha2.symm
  have hm1 : 1 ≤ q₀ * h := Nat.mul_pos hq₀p.pos hh1
  have hmT : ((q₀ * h : ℕ) : ℝ) * X ^ ((1 : ℝ) / 100) ≤ X ^ ((7 : ℝ) / 20) := by
    push_cast
    calc (q₀ : ℝ) * h * X ^ ((1 : ℝ) / 100)
        ≤ X ^ ((1 : ℝ) / 30) * X ^ ((10 : ℝ) / 33) * X ^ ((1 : ℝ) / 100) := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hX0.le _)
          exact mul_le_mul (le_trans hq₀X hlog30) hhX hh0.le (Real.rpow_nonneg hX0.le _)
      _ = X ^ ((1 : ℝ) / 30 + 10 / 33 + 1 / 100) := by
          rw [← Real.rpow_add hX0, ← Real.rpow_add hX0]
      _ ≤ X ^ ((7 : ℝ) / 20) := (Real.rpow_le_rpow_left_iff hX1).mpr (by norm_num)
  have hSin : ∀ q ∈ S, q ∈ SV.primesIoc (X ^ ((7 : ℝ) / 20)) (X ^ ((11 : ℝ) / 30)) := by
    intro q hq
    rw [hS, Finset.mem_filter] at hq
    have := hq.1
    unfold SV.qClass at this
    exact (Finset.mem_filter.mp this).1
  have hcs := q_class_sum hC0 hBT hXe hm1 hmT S hSin hcong
  have hφ : ((q₀ * h).totient : ℝ) = ((q₀ : ℝ) - 1) * (h.totient : ℝ) := by
    rw [Nat.totient_mul hcop, Nat.totient_prime hq₀p]
    push_cast [Nat.cast_sub hq₀p.one_lt.le]
    ring
  have hφh : (0 : ℝ) < h.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hq1 : (0 : ℝ) < (q₀ : ℝ) - 1 := by linarith
  have h1 : 1 / ((q₀ : ℝ) - 1) ≤ 2 / q₀ := inv_sub_one_le_two_div hq₀p.two_le
  calc ∑ q ∈ S, (1 : ℝ) / q ≤ 400 * C / ((q₀ * h).totient : ℝ) := hcs
    _ = 400 * C * (1 / ((q₀ : ℝ) - 1)) * (1 / (h.totient : ℝ)) := by
        rw [hφ]
        field_simp
    _ ≤ 400 * C * (2 / (q₀ : ℝ)) * (K / h) := by
        have h2 : (0 : ℝ) ≤ 1 / (h.totient : ℝ) := by positivity
        have h3 : (0 : ℝ) ≤ 1 / ((q₀ : ℝ) - 1) := by positivity
        have h4 : (0 : ℝ) ≤ 400 * C := by positivity
        calc 400 * C * (1 / ((q₀ : ℝ) - 1)) * (1 / (h.totient : ℝ))
            ≤ 400 * C * (2 / (q₀ : ℝ)) * (1 / (h.totient : ℝ)) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 h4) h2
          _ ≤ 400 * C * (2 / (q₀ : ℝ)) * (K / h) :=
              mul_le_mul_of_nonneg_left hphi_h (by positivity)
    _ = (800 * C * K / h) / q₀ := by
        field_simp
        ring

/-- **The swap of `eq:sv-f-sum`**: writing `𝔣(qr)` as a sum over `q₀` and exchanging the order,
`∑_{q,r} 𝔣(qr)/(qr) ≤ (∑_r 1/r) · 2β/(log log X)^2` once every inner `q`-sum is `≤ β/q₀`
(`∑_{q₀ > (log log X)^2} q₀^{-2} ≤ 2/(log log X)^2`). -/
lemma F_swap {X : ℝ} (hA1 : 1 ≤ (logIt 2 X) ^ 2) {n' h k a b : ℕ} {β : ℝ} (hβ : 0 ≤ β)
    (hq : ∀ r ∈ SV.rClass X h b, ∀ q₀ ∈ SV.primesIoc ((logIt 2 X) ^ 2) (Real.log X),
      ∑ q ∈ (SV.qClass X h a).filter (fun q => (q₀ : ℤ) ∣ (sig (q * r * k) : ℤ) -
          (sig n' : ℤ) ∧ ¬ q₀ ∣ h * sig (q * r * k)), (1 : ℝ) / q ≤ β / q₀) :
    ∑ q ∈ SV.qClass X h a, ∑ r ∈ SV.rClass X h b, SV.frak X n' h k q r / ((q : ℝ) * (r : ℝ)) ≤
      (∑ r ∈ SV.rClass X h b, (1 : ℝ) / r) * (2 * β / (logIt 2 X) ^ 2) := by
  set P := SV.primesIoc ((logIt 2 X) ^ 2) (Real.log X) with hP
  set A : ℝ := (logIt 2 X) ^ 2 with hA
  have hfr : ∀ q r : ℕ, SV.frak X n' h k q r = ∑ q₀ ∈ P,
      if ((q₀ : ℤ) ∣ (sig (q * r * k) : ℤ) - (sig n' : ℤ) ∧ ¬ q₀ ∣ h * sig (q * r * k))
      then (1 : ℝ) / q₀ else 0 := by
    intro q r
    unfold SV.frak
    rw [Finset.sum_filter]
  have hq0sq : ∑ q₀ ∈ P, ((q₀ : ℝ) ^ 2)⁻¹ ≤ 2 / A := by
    have hP' : ∀ q₀ ∈ P, ⌊A⌋₊ < q₀ := by
      intro q₀ hq₀
      rw [hP, SV.primesIoc, Finset.mem_filter] at hq₀
      exact (Nat.floor_lt (by positivity)).mpr hq₀.2.2
    calc ∑ q₀ ∈ P, ((q₀ : ℝ) ^ 2)⁻¹ ≤ 2 / ((⌊A⌋₊ : ℝ) + 1) := sum_inv_sq_le P _ hP'
      _ ≤ 2 / A := div_le_div_of_nonneg_left (by norm_num) (by linarith)
          (Nat.lt_floor_add_one A).le
  calc ∑ q ∈ SV.qClass X h a, ∑ r ∈ SV.rClass X h b, SV.frak X n' h k q r / ((q : ℝ) * (r : ℝ))
      = ∑ q ∈ SV.qClass X h a, ∑ r ∈ SV.rClass X h b, ∑ q₀ ∈ P,
          (if ((q₀ : ℤ) ∣ (sig (q * r * k) : ℤ) - (sig n' : ℤ) ∧ ¬ q₀ ∣ h * sig (q * r * k))
            then (1 : ℝ) / q₀ else 0) / ((q : ℝ) * (r : ℝ)) := by
        apply Finset.sum_congr rfl
        intro q _
        apply Finset.sum_congr rfl
        intro r _
        rw [hfr, Finset.sum_div]
    _ = ∑ r ∈ SV.rClass X h b, ∑ q₀ ∈ P, ∑ q ∈ SV.qClass X h a,
          (if ((q₀ : ℤ) ∣ (sig (q * r * k) : ℤ) - (sig n' : ℤ) ∧ ¬ q₀ ∣ h * sig (q * r * k))
            then (1 : ℝ) / q₀ else 0) / ((q : ℝ) * (r : ℝ)) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro r _
        exact Finset.sum_comm
    _ = ∑ r ∈ SV.rClass X h b, ∑ q₀ ∈ P, (1 / (r : ℝ)) * (1 / (q₀ : ℝ)) *
          ∑ q ∈ (SV.qClass X h a).filter (fun q => (q₀ : ℤ) ∣ (sig (q * r * k) : ℤ) -
            (sig n' : ℤ) ∧ ¬ q₀ ∣ h * sig (q * r * k)), (1 : ℝ) / q := by
        apply Finset.sum_congr rfl
        intro r _
        apply Finset.sum_congr rfl
        intro q₀ _
        rw [Finset.sum_filter, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q _
        split_ifs <;> ring
    _ ≤ ∑ r ∈ SV.rClass X h b, ∑ q₀ ∈ P, (1 / (r : ℝ)) * (1 / (q₀ : ℝ)) * (β / q₀) := by
        apply Finset.sum_le_sum
        intro r hr
        apply Finset.sum_le_sum
        intro q₀ hq₀
        exact mul_le_mul_of_nonneg_left (hq r hr q₀ hq₀) (by positivity)
    _ = ∑ r ∈ SV.rClass X h b, (1 / (r : ℝ)) * (β * ∑ q₀ ∈ P, ((q₀ : ℝ) ^ 2)⁻¹) := by
        apply Finset.sum_congr rfl
        intro r _
        rw [Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q₀ _
        ring
    _ ≤ ∑ r ∈ SV.rClass X h b, (1 / (r : ℝ)) * (β * (2 / A)) := by
        apply Finset.sum_le_sum
        intro r _
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hq0sq hβ) (by positivity)
    _ = (∑ r ∈ SV.rClass X h b, (1 : ℝ) / r) * (2 * β / A) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro r _
        ring

/-- The elements of `rClass` are primes of the `r`-range, pairwise congruent modulo `h`. -/
lemma rClass_facts {X : ℝ} {h b : ℕ} :
    (∀ r ∈ SV.rClass X h b, r ∈ SV.primesIoc (X ^ ((1 : ℝ) / 15)) (X ^ ((1 : ℝ) / 12))) ∧
      (∀ r ∈ SV.rClass X h b, ∀ r' ∈ SV.rClass X h b, r ≡ r' [MOD h]) := by
  constructor
  · intro r hr
    unfold SV.rClass at hr
    exact (Finset.mem_filter.mp hr).1
  · intro r hr r' hr'
    unfold SV.rClass at hr hr'
    exact (Finset.mem_filter.mp hr).2.trans (Finset.mem_filter.mp hr').2.symm

/-- The elements of `qClass` are primes of the `q`-range, pairwise congruent modulo `h`. -/
lemma qClass_facts {X : ℝ} {h a : ℕ} :
    (∀ q ∈ SV.qClass X h a, q ∈ SV.primesIoc (X ^ ((7 : ℝ) / 20)) (X ^ ((11 : ℝ) / 30))) ∧
      (∀ q ∈ SV.qClass X h a, ∀ q' ∈ SV.qClass X h a, q ≡ q' [MOD h]) := by
  constructor
  · intro q hq
    unfold SV.qClass at hq
    exact (Finset.mem_filter.mp hq).1
  · intro q hq q' hq'
    unfold SV.qClass at hq hq'
    exact (Finset.mem_filter.mp hq).2.trans (Finset.mem_filter.mp hq').2.symm

/-- The `h`-dependent setup shared by `eq:sv-f-sum` and `eq:sv-qr-sum`: `1 ≤ h`, `h ∣ s(n')` and
`1/φ(h) ≤ K/h` with `K = ζ(2) B_δ`. -/
lemma h_setup (htot : Eq_SvTotient) {D : ℕ} {B X : ℝ} {A : Finset ℕ}
    (hXb : (2 : ℝ) ^ 15 ≤ X) (hreg : ∀ M ∈ A, SV.RegularMember D B X M) {d n' h : ℕ}
    (hn' : ∃ p' : ℕ, SV.IsNPart D A X d p' n') (hhd : h ∣ aliquot n' / d) (hsq : Squarefree h) :
    1 ≤ h ∧ h ∣ aliquot n' ∧ (1 : ℝ) / (h.totient : ℝ) ≤ Real.pi ^ 2 / 6 * B / h := by
  obtain ⟨p', hN'⟩ := hn'
  obtain ⟨_, hn1', _, hRn', hab'⟩ := nPart_facts hXb hreg hN'
  obtain ⟨_, _, _, hda', han', _, _, _⟩ := regAt_basic hn1' hRn'
  have hh1 : 1 ≤ h := Nat.pos_of_ne_zero (fun h0 => by subst h0; exact not_squarefree_zero hsq)
  have hha : h ∣ aliquot n' := dvd_trans hhd (Nat.div_dvd_of_dvd hda')
  exact ⟨hh1, hha, inv_totient_le htot hh1 (Nat.pos_of_ne_zero han') hha hab'⟩

end Principia.Erdos1054.Proofs.SvSmallH

namespace Principia.Erdos1054.Proofs

open Finset

theorem link_Eq_SvFSum : Principia.Erdos1054.Spine.Link_Eq_SvFSum := by
  intro htot hBT0 δ _ _ D _ 𝒜 hfam
  obtain ⟨C, hC0, hBT⟩ := SvSmallH.BT_nonneg hBT0
  obtain ⟨_, _, B, hB, X₁, hX₁⟩ := hfam
  set K : ℝ := Real.pi ^ 2 / 6 * B with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨384000 * C ^ 2 * K ^ 2 + 4800 * C * K, max X₁ (Real.exp (120 * Real.exp 3)), ?_⟩
  intro X hX d n' h k a b hn' hhd hsq hhX hk _
  have hXa : X₁ ≤ X := le_trans (le_max_left _ _) hX
  have hXe : Real.exp (120 * Real.exp 3) ≤ X := le_trans (le_max_right _ _) hX
  obtain ⟨hX1, hlX, _, _, _, hXb⟩ := SvSmallH.bigX_facts hXe
  obtain ⟨_, _, hl2, _, _⟩ := SvSmallH.logY_facts hXe
  have hX0 : 0 < X := by linarith
  obtain ⟨_, _, hreg⟩ := hX₁ X hXa
  obtain ⟨hh1, _, hphi_h⟩ := SvSmallH.h_setup htot hXb hreg hn' hhd hsq
  have hh0 : (0 : ℝ) < h := by exact_mod_cast hh1
  have hA1 : 1 ≤ (logIt 2 X) ^ 2 := by nlinarith
  have hswap := SvSmallH.F_swap hA1 (n' := n') (k := k) (a := a) (b := b)
    (β := 800 * C * K / h) (by positivity)
    (fun r hr q₀ hq₀ => SvSmallH.F_qpart hC0 hBT hXe hK0 hh1 hhX hphi_h hk hr hq₀)
  have hRnn : 0 ≤ ∑ r ∈ SV.rClass X h b, (1 : ℝ) / r :=
    Finset.sum_nonneg (fun r _ => by positivity)
  obtain ⟨hrin, hrcong⟩ := SvSmallH.rClass_facts (X := X) (h := h) (b := b)
  have hX20 : 0 < X ^ ((1 : ℝ) / 20) := Real.rpow_pos_of_pos hX0 _
  have hl2sq : 0 < logIt 2 X ^ 2 := by positivity
  constructor
  · intro hbig
    have hrsum := SvSmallH.r_class_sum_big hXe hh1 hbig _ hrin hrcong
    calc ∑ q ∈ SV.qClass X h a, ∑ r ∈ SV.rClass X h b,
          SV.frak X n' h k q r / ((q : ℝ) * (r : ℝ))
        ≤ (∑ r ∈ SV.rClass X h b, (1 : ℝ) / r) * (2 * (800 * C * K / h) / (logIt 2 X) ^ 2) :=
          hswap
      _ ≤ (3 * Real.log X / X ^ ((1 : ℝ) / 20)) * (2 * (800 * C * K / h) / (logIt 2 X) ^ 2) :=
          mul_le_mul_of_nonneg_right hrsum (by positivity)
      _ ≤ (3 * Real.log X / X ^ ((1 : ℝ) / 20)) * (2 * (800 * C * K / h) / 1) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact div_le_div_of_nonneg_left (by positivity) (by norm_num) hA1
      _ = 4800 * C * K * (Real.log X / ((h : ℝ) * X ^ ((1 : ℝ) / 20))) := by
          field_simp
          ring
      _ ≤ (384000 * C ^ 2 * K ^ 2 + 4800 * C * K) *
            (Real.log X / ((h : ℝ) * X ^ ((1 : ℝ) / 20))) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          have : 0 ≤ 384000 * C ^ 2 * K ^ 2 := by positivity
          linarith
  · intro hsmall
    have hmT : (h : ℝ) * X ^ ((1 : ℝ) / 60) ≤ X ^ ((1 : ℝ) / 15) := by
      calc (h : ℝ) * X ^ ((1 : ℝ) / 60) ≤ X ^ ((1 : ℝ) / 20) * X ^ ((1 : ℝ) / 60) :=
            mul_le_mul_of_nonneg_right hsmall (Real.rpow_nonneg hX0.le _)
        _ = X ^ ((1 : ℝ) / 15) := by
            rw [← Real.rpow_add hX0]
            norm_num
    have hrs := SvSmallH.r_class_sum_small hC0 hBT hXe hh1 hmT _ hrin hrcong
    have hrsum : ∑ r ∈ SV.rClass X h b, (1 : ℝ) / r ≤ 240 * C * K / h := by
      calc ∑ r ∈ SV.rClass X h b, (1 : ℝ) / r ≤ 240 * C / (h.totient : ℝ) := hrs
        _ = 240 * C * (1 / (h.totient : ℝ)) := by ring
        _ ≤ 240 * C * (K / h) := mul_le_mul_of_nonneg_left hphi_h (by positivity)
        _ = 240 * C * K / h := by ring
    calc ∑ q ∈ SV.qClass X h a, ∑ r ∈ SV.rClass X h b,
          SV.frak X n' h k q r / ((q : ℝ) * (r : ℝ))
        ≤ (∑ r ∈ SV.rClass X h b, (1 : ℝ) / r) * (2 * (800 * C * K / h) / (logIt 2 X) ^ 2) :=
          hswap
      _ ≤ (240 * C * K / h) * (2 * (800 * C * K / h) / (logIt 2 X) ^ 2) :=
          mul_le_mul_of_nonneg_right hrsum (by positivity)
      _ = 384000 * C ^ 2 * K ^ 2 * (1 / ((h : ℝ) ^ 2 * logIt 2 X ^ 2)) := by
          field_simp
          ring
      _ ≤ (384000 * C ^ 2 * K ^ 2 + 4800 * C * K) * (1 / ((h : ℝ) ^ 2 * logIt 2 X ^ 2)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          have : 0 ≤ 4800 * C * K := by positivity
          linarith

end Principia.Erdos1054.Proofs

namespace Principia.Erdos1054.Proofs.SvSmallH

open Finset

/-- `∑_{q,r} (1/(qr) + L 𝔣(qr)/(qr)) = (∑_q 1/q)(∑_r 1/r) + L ∑_{q,r} 𝔣(qr)/(qr)`. -/
lemma qr_split (Q R : Finset ℕ) (f : ℕ → ℕ → ℝ) (L : ℝ) :
    ∑ q ∈ Q, ∑ r ∈ R, (1 / ((q : ℝ) * (r : ℝ)) + L * (f q r / ((q : ℝ) * (r : ℝ)))) =
      (∑ q ∈ Q, (1 : ℝ) / q) * (∑ r ∈ R, (1 : ℝ) / r) +
        L * ∑ q ∈ Q, ∑ r ∈ R, f q r / ((q : ℝ) * (r : ℝ)) := by
  rw [Finset.sum_mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  ring

/-- `log Y ≤ log log X` (so `log log X / log Y ≥ 1`) and `log log X · log Y ≥ 1`. -/
lemma l2_over_lY {X : ℝ} (hXe : Real.exp (120 * Real.exp 3) ≤ X) :
    1 ≤ logIt 2 X / Real.log (SV.Ycut X) ∧ 1 ≤ logIt 2 X * Real.log (SV.Ycut X) := by
  obtain ⟨hlY1, hlY3, hl2, _, _⟩ := logY_facts hXe
  have h32 : logIt 3 X ≤ logIt 2 X := by
    have h1 : logIt 3 X = Real.log (logIt 2 X) := rfl
    rw [h1]
    have := Real.log_le_sub_one_of_pos (show 0 < logIt 2 X by linarith)
    linarith
  constructor
  · rw [le_div_iff₀ (by linarith)]
    linarith
  · nlinarith

end Principia.Erdos1054.Proofs.SvSmallH

namespace Principia.Erdos1054.Proofs

open Finset

theorem link_Eq_SvQRSum : Principia.Erdos1054.Spine.Link_Eq_SvQRSum := by
  intro hF htot hBT0 δ hδ hδ1 D hD 𝒜 hfam
  obtain ⟨CF, XF, hFb⟩ := hF δ hδ hδ1 D hD 𝒜 hfam
  obtain ⟨C, hC0, hBT⟩ := SvSmallH.BT_nonneg hBT0
  obtain ⟨_, _, B, hB, X₁, hX₁⟩ := hfam
  set K : ℝ := Real.pi ^ 2 / 6 * B with hK
  have hK0 : 0 ≤ K := by positivity
  set CF' := max CF 0 with hCF'
  have hCF0 : 0 ≤ CF' := le_max_right _ _
  refine ⟨96000 * C ^ 2 * K ^ 2 + 1200 * C * K + CF',
    max (max X₁ XF) (Real.exp (120 * Real.exp 3)), ?_⟩
  intro X hX d n' h k a b hn' hhd hsq hhX hk hres
  have hXa : X₁ ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hXF : XF ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hXe : Real.exp (120 * Real.exp 3) ≤ X := le_trans (le_max_right _ _) hX
  obtain ⟨hX1, hlX, _, _, _, hXb⟩ := SvSmallH.bigX_facts hXe
  obtain ⟨hlY1, _, hl2, _, _⟩ := SvSmallH.logY_facts hXe
  obtain ⟨hL1, hLL⟩ := SvSmallH.l2_over_lY hXe
  have hX0 : 0 < X := by linarith
  have hlX0 : 0 < Real.log X := by linarith
  obtain ⟨_, _, hreg⟩ := hX₁ X hXa
  obtain ⟨hh1, _, hphi_h⟩ := SvSmallH.h_setup htot hXb hreg hn' hhd hsq
  have hh0 : (0 : ℝ) < h := by exact_mod_cast hh1
  obtain ⟨hF1, hF2⟩ := hFb X hXF d n' h k a b hn' hhd hsq hhX hk hres
  obtain ⟨hrin, hrcong⟩ := SvSmallH.rClass_facts (X := X) (h := h) (b := b)
  obtain ⟨hqin, hqcong⟩ := SvSmallH.qClass_facts (X := X) (h := h) (a := a)
  -- the `q`-sum without `𝔣`
  have hmTq : (h : ℝ) * X ^ ((1 : ℝ) / 100) ≤ X ^ ((7 : ℝ) / 20) := by
    calc (h : ℝ) * X ^ ((1 : ℝ) / 100) ≤ X ^ ((10 : ℝ) / 33) * X ^ ((1 : ℝ) / 100) :=
          mul_le_mul_of_nonneg_right hhX (Real.rpow_nonneg hX0.le _)
      _ = X ^ ((10 : ℝ) / 33 + 1 / 100) := (Real.rpow_add hX0 _ _).symm
      _ ≤ X ^ ((7 : ℝ) / 20) := (Real.rpow_le_rpow_left_iff hX1).mpr (by norm_num)
  have hqs := SvSmallH.q_class_sum hC0 hBT hXe hh1 hmTq _ hqin hqcong
  have hqsum : ∑ q ∈ SV.qClass X h a, (1 : ℝ) / q ≤ 400 * C * K / h := by
    calc ∑ q ∈ SV.qClass X h a, (1 : ℝ) / q ≤ 400 * C / (h.totient : ℝ) := hqs
      _ = 400 * C * (1 / (h.totient : ℝ)) := by ring
      _ ≤ 400 * C * (K / h) := mul_le_mul_of_nonneg_left hphi_h (by positivity)
      _ = 400 * C * K / h := by ring
  have hRnn : 0 ≤ ∑ r ∈ SV.rClass X h b, (1 : ℝ) / r :=
    Finset.sum_nonneg (fun r _ => by positivity)
  have hFnn : 0 ≤ ∑ q ∈ SV.qClass X h a, ∑ r ∈ SV.rClass X h b,
      SV.frak X n' h k q r / ((q : ℝ) * (r : ℝ)) := by
    apply Finset.sum_nonneg
    intro q _
    apply Finset.sum_nonneg
    intro r _
    apply div_nonneg _ (by positivity)
    unfold SV.frak
    exact Finset.sum_nonneg (fun q₀ _ => by positivity)
  have hLnn : 0 ≤ logIt 2 X / Real.log (SV.Ycut X) := by linarith
  have hX20 : 0 < X ^ ((1 : ℝ) / 20) := Real.rpow_pos_of_pos hX0 _
  constructor
  · intro hbig
    have hrsum := SvSmallH.r_class_sum_big hXe hh1 hbig _ hrin hrcong
    have hF' : ∑ q ∈ SV.qClass X h a, ∑ r ∈ SV.rClass X h b,
        SV.frak X n' h k q r / ((q : ℝ) * (r : ℝ)) ≤
        CF' * (Real.log X / ((h : ℝ) * X ^ ((1 : ℝ) / 20))) :=
      le_trans (hF1 hbig) (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    rw [SvSmallH.qr_split]
    set W := Real.log X * logIt 2 X / ((h : ℝ) * X ^ ((1 : ℝ) / 20) * Real.log (SV.Ycut X))
      with hW
    have hW' : Real.log X / ((h : ℝ) * X ^ ((1 : ℝ) / 20)) ≤ W := by
      rw [hW]
      have e : Real.log X * logIt 2 X / ((h : ℝ) * X ^ ((1 : ℝ) / 20) * Real.log (SV.Ycut X)) =
          Real.log X / ((h : ℝ) * X ^ ((1 : ℝ) / 20)) * (logIt 2 X / Real.log (SV.Ycut X)) := by
        field_simp
      rw [e]
      exact le_mul_of_one_le_right (by positivity) hL1
    have e2 : logIt 2 X / Real.log (SV.Ycut X) * (Real.log X / ((h : ℝ) * X ^ ((1 : ℝ) / 20))) =
        W := by
      rw [hW]
      field_simp
    calc (∑ q ∈ SV.qClass X h a, (1 : ℝ) / q) * (∑ r ∈ SV.rClass X h b, (1 : ℝ) / r) +
          logIt 2 X / Real.log (SV.Ycut X) * ∑ q ∈ SV.qClass X h a, ∑ r ∈ SV.rClass X h b,
            SV.frak X n' h k q r / ((q : ℝ) * (r : ℝ))
        ≤ (400 * C * K / h) * (3 * Real.log X / X ^ ((1 : ℝ) / 20)) +
            logIt 2 X / Real.log (SV.Ycut X) *
              (CF' * (Real.log X / ((h : ℝ) * X ^ ((1 : ℝ) / 20)))) := by
          apply add_le_add
          · exact mul_le_mul hqsum hrsum hRnn (by positivity)
          · exact mul_le_mul_of_nonneg_left hF' hLnn
      _ = 1200 * C * K * (Real.log X / ((h : ℝ) * X ^ ((1 : ℝ) / 20))) +
            CF' * (logIt 2 X / Real.log (SV.Ycut X) *
              (Real.log X / ((h : ℝ) * X ^ ((1 : ℝ) / 20)))) := by
          field_simp
          ring
      _ ≤ 1200 * C * K * W + CF' * W := by
          rw [e2]
          exact add_le_add (mul_le_mul_of_nonneg_left hW' (by positivity)) le_rfl
      _ ≤ (96000 * C ^ 2 * K ^ 2 + 1200 * C * K + CF') * W := by
          have hW0 : 0 ≤ W := by rw [hW]; positivity
          have : 0 ≤ 96000 * C ^ 2 * K ^ 2 * W := by positivity
          nlinarith
  · intro hsmall
    have hmT : (h : ℝ) * X ^ ((1 : ℝ) / 60) ≤ X ^ ((1 : ℝ) / 15) := by
      calc (h : ℝ) * X ^ ((1 : ℝ) / 60) ≤ X ^ ((1 : ℝ) / 20) * X ^ ((1 : ℝ) / 60) :=
            mul_le_mul_of_nonneg_right hsmall (Real.rpow_nonneg hX0.le _)
        _ = X ^ ((1 : ℝ) / 15) := by
            rw [← Real.rpow_add hX0]
            norm_num
    have hrs := SvSmallH.r_class_sum_small hC0 hBT hXe hh1 hmT _ hrin hrcong
    have hrsum : ∑ r ∈ SV.rClass X h b, (1 : ℝ) / r ≤ 240 * C * K / h := by
      calc ∑ r ∈ SV.rClass X h b, (1 : ℝ) / r ≤ 240 * C / (h.totient : ℝ) := hrs
        _ = 240 * C * (1 / (h.totient : ℝ)) := by ring
        _ ≤ 240 * C * (K / h) := mul_le_mul_of_nonneg_left hphi_h (by positivity)
        _ = 240 * C * K / h := by ring
    have hF' : ∑ q ∈ SV.qClass X h a, ∑ r ∈ SV.rClass X h b,
        SV.frak X n' h k q r / ((q : ℝ) * (r : ℝ)) ≤
        CF' * (1 / ((h : ℝ) ^ 2 * logIt 2 X ^ 2)) :=
      le_trans (hF2 hsmall) (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    rw [SvSmallH.qr_split]
    have hl2pos : 0 < logIt 2 X := by linarith
    have hkey : logIt 2 X / Real.log (SV.Ycut X) * (CF' * (1 / ((h : ℝ) ^ 2 * logIt 2 X ^ 2))) ≤
        CF' * (1 / (h : ℝ) ^ 2) := by
      have e : logIt 2 X / Real.log (SV.Ycut X) * (CF' * (1 / ((h : ℝ) ^ 2 * logIt 2 X ^ 2))) =
          CF' * (1 / (h : ℝ) ^ 2) * (1 / (logIt 2 X * Real.log (SV.Ycut X))) := by
        field_simp
      rw [e]
      apply mul_le_of_le_one_right (by positivity)
      rw [div_le_one (by positivity)]
      exact hLL
    calc (∑ q ∈ SV.qClass X h a, (1 : ℝ) / q) * (∑ r ∈ SV.rClass X h b, (1 : ℝ) / r) +
          logIt 2 X / Real.log (SV.Ycut X) * ∑ q ∈ SV.qClass X h a, ∑ r ∈ SV.rClass X h b,
            SV.frak X n' h k q r / ((q : ℝ) * (r : ℝ))
        ≤ (400 * C * K / h) * (240 * C * K / h) +
            logIt 2 X / Real.log (SV.Ycut X) * (CF' * (1 / ((h : ℝ) ^ 2 * logIt 2 X ^ 2))) := by
          apply add_le_add
          · exact mul_le_mul hqsum hrsum hRnn (by positivity)
          · exact mul_le_mul_of_nonneg_left hF' hLnn
      _ ≤ (400 * C * K / h) * (240 * C * K / h) + CF' * (1 / (h : ℝ) ^ 2) := by
          linarith
      _ = (96000 * C ^ 2 * K ^ 2 + CF') * (1 / (h : ℝ) ^ 2) := by
          field_simp
          ring
      _ ≤ (96000 * C ^ 2 * K ^ 2 + 1200 * C * K + CF') * (1 / (h : ℝ) ^ 2) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          have : 0 ≤ 1200 * C * K := by positivity
          linarith

end Principia.Erdos1054.Proofs

namespace Principia.Erdos1054.Proofs.SvSmallH

open Finset

/-! ## Divisor sums for the `h`-summation -/

/-- `σ(m)/m = ∑_{e ∣ m} 1/e`. -/
lemma abundancy_eq_sum {m : ℕ} (hm : 1 ≤ m) : abundancy m = ∑ e ∈ m.divisors, (1 : ℝ) / e := by
  unfold abundancy
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have h1 : (sig m : ℝ) = ∑ e ∈ m.divisors, ((m / e : ℕ) : ℝ) := by
    show ((ArithmeticFunction.sigma 1 m : ℕ) : ℝ) = _
    rw [ArithmeticFunction.sigma_one_apply, ← Nat.sum_div_divisors m (fun d => d), Nat.cast_sum]
  rw [h1, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro e he
  have hed : e ∣ m := Nat.dvd_of_mem_divisors he
  have he0 : (e : ℝ) ≠ 0 := by
    have := Nat.pos_of_mem_divisors he
    positivity
  rw [Nat.cast_div hed he0]
  field_simp

lemma abundancy_nonneg (m : ℕ) : 0 ≤ abundancy m := by
  unfold abundancy
  positivity

/-- `σ(v)/v ≤ σ(m)/m` for `v ∣ m`. -/
lemma abundancy_mono {m M : ℕ} (hm : 1 ≤ m) (hM : 1 ≤ M) (hmM : m ∣ M) :
    abundancy m ≤ abundancy M := by
  rw [abundancy_eq_sum hm, abundancy_eq_sum hM]
  apply Finset.sum_le_sum_of_subset_of_nonneg (Nat.divisors_subset_of_dvd (by omega) hmM)
  intro i _ _
  positivity

/-- `∑_{h ∣ m} τ(h)/h ≤ (σ(m)/m)^2` (EP1054.tex lines 1852–1855). -/
lemma sum_tau_div_le {m : ℕ} (hm : 1 ≤ m) :
    ∑ h ∈ m.divisors, (h.divisors.card : ℝ) / h ≤ abundancy m ^ 2 := by
  classical
  rw [abundancy_eq_sum hm, sq, Finset.sum_mul_sum]
  have hL : ∑ h ∈ m.divisors, (h.divisors.card : ℝ) / h =
      ∑ x ∈ m.divisors.sigma (fun h => h.divisors), (1 : ℝ) / (x.1 : ℕ) := by
    rw [Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro h _
    show (h.divisors.card : ℝ) / h = ∑ s ∈ h.divisors, (1 : ℝ) / h
    rw [Finset.sum_const, nsmul_eq_mul]
    ring
  rw [hL]
  have hR : ∑ e ∈ m.divisors, ∑ f ∈ m.divisors, (1 : ℝ) / e * (1 / f) =
      ∑ y ∈ m.divisors ×ˢ m.divisors, (1 : ℝ) / (((y.1 : ℕ) : ℝ) * ((y.2 : ℕ) : ℝ)) := by
    rw [Finset.sum_product]
    apply Finset.sum_congr rfl
    intro e _
    apply Finset.sum_congr rfl
    intro f _
    rw [one_div_mul_one_div]
  rw [hR]
  set φ : (_ : ℕ) × ℕ → ℕ × ℕ := fun x => (x.2, x.1 / x.2) with hφ
  have hinj : Set.InjOn φ (m.divisors.sigma (fun h => h.divisors) : Set ((_ : ℕ) × ℕ)) := by
    rintro ⟨h, e⟩ hx ⟨h', e'⟩ hy hxy
    rw [Finset.mem_coe, Finset.mem_sigma] at hx hy
    simp only [hφ, Prod.mk.injEq] at hxy
    obtain ⟨h1, h2⟩ := hxy
    have hd : e ∣ h := Nat.dvd_of_mem_divisors hx.2
    have hd' : e' ∣ h' := Nat.dvd_of_mem_divisors hy.2
    have hhh : h = h' := by
      calc h = e * (h / e) := (Nat.mul_div_cancel' hd).symm
        _ = e' * (h' / e') := by rw [h2, h1]
        _ = h' := Nat.mul_div_cancel' hd'
    subst hhh
    subst h1
    rfl
  calc ∑ x ∈ m.divisors.sigma (fun h => h.divisors), (1 : ℝ) / (x.1 : ℕ)
      = ∑ x ∈ m.divisors.sigma (fun h => h.divisors),
          (1 : ℝ) / ((((φ x).1 : ℕ) : ℝ) * (((φ x).2 : ℕ) : ℝ)) := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [Finset.mem_sigma] at hx
        have hd : x.2 ∣ x.1 := Nat.dvd_of_mem_divisors hx.2
        simp only [hφ]
        rw [← Nat.cast_mul, Nat.mul_div_cancel' hd]
    _ = ∑ y ∈ (m.divisors.sigma (fun h => h.divisors)).image φ,
          (1 : ℝ) / (((y.1 : ℕ) : ℝ) * ((y.2 : ℕ) : ℝ)) := by
        rw [Finset.sum_image hinj]
    _ ≤ ∑ y ∈ m.divisors ×ˢ m.divisors, (1 : ℝ) / (((y.1 : ℕ) : ℝ) * ((y.2 : ℕ) : ℝ)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro y hy
          rw [Finset.mem_image] at hy
          obtain ⟨x, hx, rfl⟩ := hy
          rw [Finset.mem_sigma] at hx
          have hxm := Nat.dvd_of_mem_divisors hx.1
          have hex := Nat.dvd_of_mem_divisors hx.2
          simp only [hφ]
          rw [Finset.mem_product, Nat.mem_divisors, Nat.mem_divisors]
          exact ⟨⟨dvd_trans hex hxm, by omega⟩, ⟨dvd_trans (Nat.div_dvd_of_dvd hex) hxm, by omega⟩⟩
        · intro y _ _
          positivity

/-- `∑_{h ∈ S} τ(h) ≤ τ(m)^2` for `S ⊆ divisors m`. -/
lemma sum_tau_le {m : ℕ} (hm : m ≠ 0) (S : Finset ℕ) (hS : S ⊆ m.divisors) :
    ∑ h ∈ S, (h.divisors.card : ℝ) ≤ (m.divisors.card : ℝ) ^ 2 := by
  calc ∑ h ∈ S, (h.divisors.card : ℝ) ≤ ∑ h ∈ S, (m.divisors.card : ℝ) := by
        apply Finset.sum_le_sum
        intro h hh
        have hd := Nat.dvd_of_mem_divisors (hS hh)
        exact_mod_cast Finset.card_le_card (Nat.divisors_subset_of_dvd hm hd)
    _ = (S.card : ℝ) * (m.divisors.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (m.divisors.card : ℝ) * (m.divisors.card : ℝ) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast Finset.card_le_card hS
    _ = (m.divisors.card : ℝ) ^ 2 := by ring

/-- `σ(n) ≤ n^2`. -/
lemma sig_le_sq (n : ℕ) : sig n ≤ n ^ 2 := by
  show ArithmeticFunction.sigma 1 n ≤ n ^ 2
  rw [ArithmeticFunction.sigma_one_apply]
  calc ∑ d ∈ n.divisors, d ≤ ∑ d ∈ n.divisors, n :=
        Finset.sum_le_sum (fun d hd => Nat.divisor_le hd)
    _ = n.divisors.card * n := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ n * n := Nat.mul_le_mul_right _ (Nat.card_divisors_le_self n)
    _ = n ^ 2 := (sq n).symm

/-! ## Finite sums: `biUnion` and injections -/

/-- A nonnegative sum over a `biUnion` is at most the iterated sum. -/
lemma sum_biUnion_le_of_nonneg {ι α : Type*} [DecidableEq ι] [DecidableEq α] (s : Finset ι)
    (t : ι → Finset α) (f : α → ℝ) (hf : ∀ x ∈ s.biUnion t, 0 ≤ f x) :
    ∑ x ∈ s.biUnion t, f x ≤ ∑ i ∈ s, ∑ x ∈ t i, f x := by
  revert hf
  refine Finset.induction_on s ?_ ?_
  · intro _
    simp
  · intro a s ha ih hf
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    have hf' : ∀ x ∈ s.biUnion t, 0 ≤ f x := fun x hx =>
      hf x (by rw [Finset.biUnion_insert]; exact Finset.mem_union_right _ hx)
    have hinter := Finset.sum_union_inter (s₁ := t a) (s₂ := s.biUnion t) (f := f)
    have hi0 : 0 ≤ ∑ x ∈ t a ∩ s.biUnion t, f x := Finset.sum_nonneg (fun x hx =>
      hf x (by rw [Finset.biUnion_insert]; exact Finset.mem_union_left _ (Finset.mem_inter.mp hx).1))
    linarith [ih hf']

/-- A sum over `s` is at most a nonnegative sum over `t` when `s` injects into `t` with
pointwise domination. -/
lemma sum_le_sum_of_injOn' {α β : Type*} [DecidableEq β] (s : Finset α) (t : Finset β)
    (φ : α → β) (hmaps : ∀ x ∈ s, φ x ∈ t) (hinj : Set.InjOn φ s) (w : α → ℝ) (F : β → ℝ)
    (hF : ∀ y ∈ t, 0 ≤ F y) (hw : ∀ x ∈ s, w x ≤ F (φ x)) :
    ∑ x ∈ s, w x ≤ ∑ y ∈ t, F y := by
  calc ∑ x ∈ s, w x ≤ ∑ x ∈ s, F (φ x) := Finset.sum_le_sum hw
    _ = ∑ y ∈ s.image φ, F y := (Finset.sum_image hinj).symm
    _ ≤ ∑ y ∈ t, F y := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro y hy
          rw [Finset.mem_image] at hy
          obtain ⟨x, hx, rfl⟩ := hy
          exact hmaps x hx
        · intro y hy _
          exact hF y hy

end Principia.Erdos1054.Proofs.SvSmallH

namespace Principia.Erdos1054.Proofs.SvSmallH

open Finset

/-! ## The regrouped sum of the small-`h` case -/

/-- The weight of one collision after `eq:sv-intermediate-totient`, as a function of
`(n', h, k, q, r)`: `(h/n')(1/k)(1/(qr) + L 𝔣(qr)/(qr))`. -/
noncomputable def Psi (X L : ℝ) (n' h k q r : ℕ) : ℝ :=
  (h : ℝ) / n' * (1 / (k : ℝ)) *
    (1 / ((q : ℝ) * (r : ℝ)) + L * (SV.frak X n' h k q r / ((q : ℝ) * (r : ℝ))))

lemma frak_nonneg (X : ℝ) (n' h k q r : ℕ) : 0 ≤ SV.frak X n' h k q r := by
  unfold SV.frak
  exact Finset.sum_nonneg (fun q₀ _ => by positivity)

lemma Psi_nonneg {X L : ℝ} (hL : 0 ≤ L) (n' h k q r : ℕ) : 0 ≤ Psi X L n' h k q r := by
  unfold Psi
  have := frak_nonneg X n' h k q r
  positivity

open Classical in
/-- The `n'` that are `n`-parts of members of the class `d`. -/
noncomputable def Nset (D : ℕ) (A : Finset ℕ) (X : ℝ) (d : ℕ) : Finset ℕ :=
  (Finset.Icc 1 ⌊X⌋₊).filter (fun n' => ∃ p', SV.IsNPart D A X d p' n')

open Classical in
/-- The admissible `h ∣ s(n')/d` of the small-`h` range. -/
noncomputable def Hset (X : ℝ) (d n' : ℕ) : Finset ℕ :=
  (aliquot n' / d).divisors.filter (fun h => Squarefree h ∧ (h : ℝ) ≤ X ^ ((10 : ℝ) / 33))

/-- The `k ∈ SV.kSet X d` with `k`, `σ(k)` units modulo `h`. -/
noncomputable def Kset (X : ℝ) (d h : ℕ) : Finset ℕ :=
  (SV.kSet X d).filter (fun k => Nat.Coprime k h ∧ Nat.Coprime (sig k) h)

open Classical in
/-- The `(q, r)` of the two prime ranges satisfying the residue congruences for `(h, n', k)`. -/
noncomputable def Wset (X : ℝ) (h n' k : ℕ) : Finset (ℕ × ℕ) :=
  (SV.primesIoc (X ^ ((7 : ℝ) / 20)) (X ^ ((11 : ℝ) / 30)) ×ˢ
    SV.primesIoc (X ^ ((1 : ℝ) / 15)) (X ^ ((1 : ℝ) / 12))).filter
    (fun qr => SV.ResiduePair h n' k qr.1 qr.2)

open Classical in
/-- **At most `τ(h)` residue pairs** (EP1054.tex lines 1756–1762): for fixed `n', h, k` the
`(q, r)` lie in the classes `(q mod h, r mod h)` of residue pairs, each carrying at most `β`. -/
lemma residue_class_bound {X : ℝ} {h n' k : ℕ} (hh1 : 1 ≤ h) (G : ℕ → ℕ → ℝ)
    (hG : ∀ q r, 0 ≤ G q r) {β : ℝ} (hβ : 0 ≤ β)
    (hQR : ∀ a b : ℕ, SV.ResiduePair h n' k a b →
      ∑ q ∈ SV.qClass X h a, ∑ r ∈ SV.rClass X h b, G q r ≤ β)
    (hcount : ((Finset.range h ×ˢ Finset.range h).filter
        (fun ab : ℕ × ℕ => SV.ResiduePair h n' k ab.1 ab.2)).card ≤ h.divisors.card) :
    ∑ qr ∈ Wset X h n' k, G qr.1 qr.2 ≤ (h.divisors.card : ℝ) * β := by
  set RPs := (Finset.range h ×ˢ Finset.range h).filter
    (fun ab : ℕ × ℕ => SV.ResiduePair h n' k ab.1 ab.2) with hRPs
  have hsub : Wset X h n' k ⊆
      RPs.biUnion (fun ab => SV.qClass X h ab.1 ×ˢ SV.rClass X h ab.2) := by
    intro qr hqr
    unfold Wset at hqr
    rw [Finset.mem_filter, Finset.mem_product] at hqr
    obtain ⟨⟨hq, hr⟩, hres⟩ := hqr
    rw [Finset.mem_biUnion]
    refine ⟨(qr.1 % h, qr.2 % h), ?_, ?_⟩
    · rw [hRPs, Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
      refine ⟨⟨Nat.mod_lt _ (by omega), Nat.mod_lt _ (by omega)⟩, ?_⟩
      obtain ⟨e1, e2⟩ := hres
      have hqm := Nat.mod_modEq qr.1 h
      have hrm := Nat.mod_modEq qr.2 h
      exact ⟨((hqm.mul hrm).mul_right k).trans e1,
        (((hqm.add_right 1).mul (hrm.add_right 1)).mul_right _).trans e2⟩
    · rw [Finset.mem_product]
      unfold SV.qClass SV.rClass
      rw [Finset.mem_filter, Finset.mem_filter]
      exact ⟨⟨hq, (Nat.mod_modEq qr.1 h).symm⟩, ⟨hr, (Nat.mod_modEq qr.2 h).symm⟩⟩
  calc ∑ qr ∈ Wset X h n' k, G qr.1 qr.2
      ≤ ∑ qr ∈ RPs.biUnion (fun ab => SV.qClass X h ab.1 ×ˢ SV.rClass X h ab.2), G qr.1 qr.2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => hG _ _)
    _ ≤ ∑ ab ∈ RPs, ∑ qr ∈ SV.qClass X h ab.1 ×ˢ SV.rClass X h ab.2, G qr.1 qr.2 :=
        sum_biUnion_le_of_nonneg _ _ (fun qr : ℕ × ℕ => G qr.1 qr.2) (fun x _ => hG _ _)
    _ = ∑ ab ∈ RPs, ∑ q ∈ SV.qClass X h ab.1, ∑ r ∈ SV.rClass X h ab.2, G q r := by
        apply Finset.sum_congr rfl
        intro ab _
        rw [Finset.sum_product]
    _ ≤ ∑ ab ∈ RPs, β := by
        apply Finset.sum_le_sum
        intro ab hab
        rw [hRPs, Finset.mem_filter] at hab
        exact hQR ab.1 ab.2 hab.2
    _ = (RPs.card : ℝ) * β := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (h.divisors.card : ℝ) * β := mul_le_mul_of_nonneg_right (by exact_mod_cast hcount) hβ

/-- **The `h`-sum** (EP1054.tex lines 1841–1857): with `β(h) = C/h^2 + C W/h`,
`∑_{h ∈ S} h τ(h) β(h) ≤ C B^2 + C W T^2` when `S ⊆ divisors m`, `σ(m)/m ≤ B`, `τ(m) ≤ T`. -/
lemma h_sum_bound {m : ℕ} (hm : 1 ≤ m) (S : Finset ℕ) (hS : S ⊆ m.divisors) {B C W T : ℝ}
    (hB : abundancy m ≤ B) (hC : 0 ≤ C) (hW : 0 ≤ W) (hT : (m.divisors.card : ℝ) ≤ T) :
    ∑ h ∈ S, (h : ℝ) * (h.divisors.card : ℝ) * (C / (h : ℝ) ^ 2 + C * W / h) ≤
      C * B ^ 2 + C * W * T ^ 2 := by
  have hh : ∀ h ∈ S, (1 : ℝ) ≤ h := by
    intro h hh
    exact_mod_cast Nat.pos_of_mem_divisors (hS hh)
  have e : ∑ h ∈ S, (h : ℝ) * (h.divisors.card : ℝ) * (C / (h : ℝ) ^ 2 + C * W / h) =
      C * ∑ h ∈ S, (h.divisors.card : ℝ) / h + C * W * ∑ h ∈ S, (h.divisors.card : ℝ) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro h hmem
    have := hh h hmem
    field_simp
  rw [e]
  have h1 : ∑ h ∈ S, (h.divisors.card : ℝ) / h ≤ B ^ 2 := by
    calc ∑ h ∈ S, (h.divisors.card : ℝ) / h ≤ ∑ h ∈ m.divisors, (h.divisors.card : ℝ) / h :=
          Finset.sum_le_sum_of_subset_of_nonneg hS (fun _ _ _ => by positivity)
      _ ≤ abundancy m ^ 2 := sum_tau_div_le hm
      _ ≤ B ^ 2 := pow_le_pow_left₀ (abundancy_nonneg m) hB 2
  have h2 : ∑ h ∈ S, (h.divisors.card : ℝ) ≤ T ^ 2 :=
    le_trans (sum_tau_le (by omega) S hS) (pow_le_pow_left₀ (by positivity) hT 2)
  have hCW : 0 ≤ C * W := mul_nonneg hC hW
  nlinarith

/-- The factor ranges of a member tuple: `q`, `r` in their prime ranges and `k ∈ SV.kSet X d`. -/
lemma member_ranges {D : ℕ} {B X : ℝ} {A : Finset ℕ}
    (hreg : ∀ M ∈ A, SV.RegularMember D B X M) {d p q r k : ℕ}
    (hm : SV.MemberTuple D A X d p q r k) :
    q ∈ SV.primesIoc (X ^ ((7 : ℝ) / 20)) (X ^ ((11 : ℝ) / 30)) ∧
      r ∈ SV.primesIoc (X ^ ((1 : ℝ) / 15)) (X ^ ((1 : ℝ) / 12)) ∧ k ∈ SV.kSet X d := by
  obtain ⟨hRk, _, _, _, _, _, _⟩ := member_regular hreg hm
  obtain ⟨_, hq, hr, _, hk1, hk2, hr1, hr2, hq1, hq2, _, _⟩ := hm.1
  unfold SV.primesIoc SV.kSet
  rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_filter, Finset.mem_Iic, Finset.mem_Iic,
    Finset.mem_Iic]
  exact ⟨⟨Nat.le_floor hq2, hq, hq1⟩, ⟨Nat.le_floor hr2, hr, hr1⟩,
    ⟨Nat.le_floor hk2, hk1, hRk.2.1.symm⟩⟩

/-- `∑_{n' ∈ Nset} 1/n'` is at most the triple sum of `eq:sv-m-reciprocal`. -/
lemma Nset_recip {D : ℕ} {B X : ℝ} {A : Finset ℕ}
    (hreg : ∀ M ∈ A, SV.RegularMember D B X M) (d : ℕ) :
    ∑ n' ∈ Nset D A X d, (1 : ℝ) / n' ≤
      ∑ q ∈ SV.primesIoc (X ^ ((7 : ℝ) / 20)) (X ^ ((11 : ℝ) / 30)),
        ∑ r ∈ SV.primesIoc (X ^ ((1 : ℝ) / 15)) (X ^ ((1 : ℝ) / 12)),
          ∑ k ∈ SV.kSet X d, (1 : ℝ) / ((q : ℝ) * (r : ℝ) * (k : ℝ)) := by
  classical
  have hch : ∀ n' : ℕ, (∃ p', SV.IsNPart D A X d p' n') → ∃ t : ℕ × ℕ × ℕ,
      (∃ p', SV.MemberTuple D A X d p' t.1 t.2.1 t.2.2) ∧ n' = t.1 * t.2.1 * t.2.2 := by
    rintro n' ⟨p', q, r, k, hm, rfl⟩
    exact ⟨(q, r, k), ⟨p', hm⟩, rfl⟩
  choose! τ hτ using hch
  have hmem : ∀ n' ∈ Nset D A X d, ∃ p', SV.IsNPart D A X d p' n' := by
    intro n' hn'
    unfold Nset at hn'
    exact (Finset.mem_filter.mp hn').2
  rw [← Finset.sum_product', ← Finset.sum_product']
  refine sum_le_sum_of_injOn' _ _ (fun n' => (((τ n').1, (τ n').2.1), (τ n').2.2)) ?_ ?_ _
    (fun y : (ℕ × ℕ) × ℕ => (1 : ℝ) / ((y.1.1 : ℝ) * (y.1.2 : ℝ) * (y.2 : ℝ))) ?_ ?_
  · intro n' hn'
    obtain ⟨⟨p', hm⟩, _⟩ := hτ n' (hmem n' hn')
    obtain ⟨h1, h2, h3⟩ := member_ranges hreg hm
    rw [Finset.mem_product, Finset.mem_product]
    exact ⟨⟨h1, h2⟩, h3⟩
  · intro x hx y hy hxy
    simp only [Prod.mk.injEq] at hxy
    obtain ⟨⟨h1, h2⟩, h3⟩ := hxy
    rw [(hτ x (hmem x hx)).2, (hτ y (hmem y hy)).2, h1, h2, h3]
  · intro y _
    positivity
  · intro n' hn'
    have e := (hτ n' (hmem n' hn')).2
    have e' : (n' : ℝ) = ((τ n').1 : ℝ) * ((τ n').2.1 : ℝ) * ((τ n').2.2 : ℝ) := by
      exact_mod_cast e
    simp only
    rw [e']

end Principia.Erdos1054.Proofs.SvSmallH

namespace Principia.Erdos1054.Proofs.SvSmallH

open Finset

/-- The flattened index set `(n', h, k, q, r)` of the regrouped small-`h` sum. -/
noncomputable def S5set (D : ℕ) (A : Finset ℕ) (X : ℝ) (d : ℕ) : Finset (ℕ × ℕ × ℕ × ℕ × ℕ) :=
  (Nset D A X d).biUnion (fun n' => (Hset X d n').biUnion (fun h => (Kset X d h).biUnion
    (fun k => (Wset X h n' k).image (fun qr => (n', h, k, qr.1, qr.2)))))

lemma S5_sum_le {D : ℕ} {A : Finset ℕ} {X L : ℝ} {d : ℕ} (hL : 0 ≤ L) :
    ∑ y ∈ S5set D A X d, Psi X L y.1 y.2.1 y.2.2.1 y.2.2.2.1 y.2.2.2.2 ≤
      ∑ n' ∈ Nset D A X d, ∑ h ∈ Hset X d n', ∑ k ∈ Kset X d h,
        ∑ qr ∈ Wset X h n' k, Psi X L n' h k qr.1 qr.2 := by
  unfold S5set
  set f := fun y : ℕ × ℕ × ℕ × ℕ × ℕ => Psi X L y.1 y.2.1 y.2.2.1 y.2.2.2.1 y.2.2.2.2 with hf
  have hf0 : ∀ y, 0 ≤ f y := fun y => Psi_nonneg hL _ _ _ _ _
  refine le_trans (sum_biUnion_le_of_nonneg _ _ f (fun y _ => hf0 y)) ?_
  apply Finset.sum_le_sum
  intro n' _
  refine le_trans (sum_biUnion_le_of_nonneg _ _ f (fun y _ => hf0 y)) ?_
  apply Finset.sum_le_sum
  intro h _
  refine le_trans (sum_biUnion_le_of_nonneg _ _ f (fun y _ => hf0 y)) ?_
  apply Finset.sum_le_sum
  intro k _
  rw [Finset.sum_image]
  intro a _ b _ hab
  simp only [Prod.mk.injEq] at hab
  exact Prod.ext hab.2.2.2.1 hab.2.2.2.2

/-- **The regrouping of the small-`h` sum** (EP1054.tex lines 1733–1835): after
`A'_{3,2} → A''_{3,2}` (constant `C₁`) and `eq:sv-intermediate-totient` (constant `C₂`), each
collision pair `(n, n')` with `n = qrk` contributes at most `C₁C₂ d Ψ(n', h, k, q, r)`, and
`(n, n') ↦ (n', h, k, q, r)` is injective into the index set `n' ∈ Nset`, `h ∈ Hset`, `k ∈ Kset`,
`(q, r) ∈ Wset` (squarefree `h`; `k, σ(k)` units mod `h`; the residue congruences). -/
lemma pair_regroup {D : ℕ} {B X : ℝ} {A : Finset ℕ} {d : ℕ} (hXb : (2 : ℝ) ^ 15 ≤ X)
    (hreg : ∀ M ∈ A, SV.RegularMember D B X M) {C₁ C₂ L : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hL : 0 ≤ L)
    (hA322 : ∀ n n', SV.CollisionPair D A X d n n' →
      ((SV.gcdS n n' / d : ℕ) : ℝ) ≤ X ^ ((10 : ℝ) / 33) →
        SV.ratio32 X n n' ≤ C₁ * SV.ratio322 X n n')
    (hsqf : ∀ n n', SV.CollisionPair D A X d n n' →
      ((SV.gcdS n n' / d : ℕ) : ℝ) ≤ X ^ ((10 : ℝ) / 33) → Squarefree (SV.gcdS n n' / d))
    (hres : ∀ p q r k n', SV.MemberTuple D A X d p q r k →
      SV.CollisionPair D A X d (q * r * k) n' →
      ((SV.gcdS (q * r * k) n' / d : ℕ) : ℝ) ≤ X ^ ((10 : ℝ) / 33) →
        Nat.Coprime k (SV.gcdS (q * r * k) n' / d) ∧
          Nat.Coprime (sig k) (SV.gcdS (q * r * k) n' / d) ∧
          SV.ResiduePair (SV.gcdS (q * r * k) n' / d) n' k q r)
    (hit : ∀ p q r k n', SV.MemberTuple D A X d p q r k →
      SV.CollisionPair D A X d (q * r * k) n' →
      ((SV.gcdS (q * r * k) n' / d : ℕ) : ℝ) ≤ X ^ ((10 : ℝ) / 33) →
        SV.ratio322 X (q * r * k) n' ≤
          C₂ * (1 + L * SV.frak X n' (SV.gcdS (q * r * k) n' / d) k q r)) :
    SV.reducedCollisionSum D A X d (fun h => (h : ℝ) ≤ X ^ ((10 : ℝ) / 33)) ≤
      C₁ * C₂ * d * ∑ n' ∈ Nset D A X d, ∑ h ∈ Hset X d n', ∑ k ∈ Kset X d h,
        ∑ qr ∈ Wset X h n' k, Psi X L n' h k qr.1 qr.2 := by
  classical
  have hch : ∀ n : ℕ, (∃ p, SV.IsNPart D A X d p n) → ∃ t : ℕ × ℕ × ℕ × ℕ,
      SV.MemberTuple D A X d t.1 t.2.1 t.2.2.1 t.2.2.2 ∧ n = t.2.1 * t.2.2.1 * t.2.2.2 := by
    rintro n ⟨p, q, r, k, hm, rfl⟩
    exact ⟨(p, q, r, k), hm, rfl⟩
  choose! τ hτ using hch
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  refine le_trans ?_ (mul_le_mul_of_nonneg_left (S5_sum_le (D := D) (A := A) (X := X) (d := d) hL)
    (by positivity))
  rw [Finset.mul_sum]
  unfold SV.reducedCollisionSum
  refine sum_le_sum_of_injOn' _ _ (fun nn : ℕ × ℕ => (nn.2, SV.gcdS nn.1 nn.2 / d,
      (τ nn.1).2.2.2, (τ nn.1).2.1, (τ nn.1).2.2.1)) ?_ ?_ _ _ ?_ ?_
  · rintro ⟨n, n'⟩ hnn
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hnn
    obtain ⟨⟨_, ⟨hn'1, hn'X⟩⟩, hC, hH⟩ := hnn
    simp only at hC hH ⊢
    have hNP : ∃ p, SV.IsNPart D A X d p n := by
      obtain ⟨_, p, _, hN, _, _⟩ := hC
      exact ⟨p, hN⟩
    have hτn := hτ n hNP
    rcases ht : τ n with ⟨p, q, r, k⟩
    rw [ht] at hτn
    simp only at hτn
    obtain ⟨hm, rfl⟩ := hτn
    simp only
    obtain ⟨_, _, p', hN2⟩ := id hC
    obtain ⟨_, hn1', _, hRn', _⟩ := nPart_facts hXb hreg hN2.2.1
    obtain ⟨_, _, hRn, _, _, _, _⟩ := member_regular hreg hm
    obtain ⟨_, hq, hr, hk, _, _, _, _, _, _⟩ := tuple_facts hXb hm.1
    have hn1 : 1 ≤ q * r * k := Nat.mul_pos (Nat.mul_pos hq.pos hr.pos) hk
    obtain ⟨hd1, _, _, hda, _, _, _, _⟩ := regAt_basic hn1 hRn
    obtain ⟨_, _, _, hda', han', _, _, _⟩ := regAt_basic hn1' hRn'
    have hdg : d ∣ SV.gcdS (q * r * k) n' := Nat.dvd_gcd hda hda'
    obtain ⟨hck, hcsk, hrp⟩ := hres p q r k n' hm hC hH
    obtain ⟨hqR, hrR, hkS⟩ := member_ranges hreg hm
    unfold S5set
    rw [Finset.mem_biUnion]
    refine ⟨n', ?_, ?_⟩
    · unfold Nset
      rw [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hn'1, hn'X⟩, p', hN2.2.1⟩
    rw [Finset.mem_biUnion]
    refine ⟨SV.gcdS (q * r * k) n' / d, ?_, ?_⟩
    · unfold Hset
      rw [Finset.mem_filter, Nat.mem_divisors]
      refine ⟨⟨Nat.div_dvd_div hdg (Nat.gcd_dvd_right _ _), ?_⟩, hsqf _ _ hC hH, hH⟩
      exact (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero han') hda') hd1).ne'
    rw [Finset.mem_biUnion]
    refine ⟨k, ?_, ?_⟩
    · unfold Kset
      rw [Finset.mem_filter]
      exact ⟨hkS, hck, hcsk⟩
    rw [Finset.mem_image]
    refine ⟨(q, r), ?_, rfl⟩
    unfold Wset
    rw [Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨hqR, hrR⟩, hrp⟩
  · rintro ⟨n, n'⟩ hx ⟨m, m'⟩ hy hxy
    rw [Finset.mem_coe, Finset.mem_filter] at hx hy
    have hNPx : ∃ p, SV.IsNPart D A X d p n := by
      obtain ⟨_, p, _, hN, _, _⟩ := hx.2.1
      exact ⟨p, hN⟩
    have hNPy : ∃ p, SV.IsNPart D A X d p m := by
      obtain ⟨_, p, _, hN, _, _⟩ := hy.2.1
      exact ⟨p, hN⟩
    simp only [Prod.mk.injEq] at hxy
    obtain ⟨h1, _, h3, h4, h5⟩ := hxy
    have e1 := (hτ n hNPx).2
    have e2 := (hτ m hNPy).2
    have : n = m := by rw [e1, e2, h3, h4, h5]
    rw [this, h1]
  · intro y _
    exact mul_nonneg (by positivity) (Psi_nonneg hL _ _ _ _ _)
  · rintro ⟨n, n'⟩ hnn
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hnn
    obtain ⟨⟨_, ⟨hn'1, _⟩⟩, hC, hH⟩ := hnn
    simp only at hC hH ⊢
    have hNP : ∃ p, SV.IsNPart D A X d p n := by
      obtain ⟨_, p, _, hN, _, _⟩ := hC
      exact ⟨p, hN⟩
    have hτn := hτ n hNP
    rcases ht : τ n with ⟨p, q, r, k⟩
    rw [ht] at hτn
    simp only at hτn
    obtain ⟨hm, rfl⟩ := hτn
    simp only
    obtain ⟨_, _, p', hN2⟩ := id hC
    obtain ⟨_, hn1', _, hRn', _⟩ := nPart_facts hXb hreg hN2.2.1
    obtain ⟨_, _, hRn, _, _, _, _⟩ := member_regular hreg hm
    obtain ⟨_, hq, hr, hk, _, _, _, _, _, _⟩ := tuple_facts hXb hm.1
    have hn1 : 1 ≤ q * r * k := Nat.mul_pos (Nat.mul_pos hq.pos hr.pos) hk
    obtain ⟨_, _, _, hda, _, _, _, _⟩ := regAt_basic hn1 hRn
    obtain ⟨_, _, _, hda', _, _, _, _⟩ := regAt_basic hn1' hRn'
    have hdg : d ∣ SV.gcdS (q * r * k) n' := Nat.dvd_gcd hda hda'
    have hgR : ((SV.gcdS (q * r * k) n' : ℕ) : ℝ) = (d : ℝ) * ((SV.gcdS (q * r * k) n' / d : ℕ) : ℝ) := by
      exact_mod_cast (Nat.mul_div_cancel' hdg).symm
    have hA := hA322 _ _ hC hH
    have hI := hit p q r k n' hm hC hH
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
    have hr0 : (0 : ℝ) < r := by exact_mod_cast hr.pos
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    have hn0 : (0 : ℝ) < n' := by exact_mod_cast hn'1
    have hw0 : (0 : ℝ) ≤ ((SV.gcdS (q * r * k) n' : ℕ) : ℝ) / (((q * r * k : ℕ) : ℝ) * (n' : ℝ)) := by
      positivity
    calc ((SV.gcdS (q * r * k) n' : ℕ) : ℝ) / (((q * r * k : ℕ) : ℝ) * (n' : ℝ)) *
          SV.ratio32 X (q * r * k) n'
        ≤ ((SV.gcdS (q * r * k) n' : ℕ) : ℝ) / (((q * r * k : ℕ) : ℝ) * (n' : ℝ)) *
            (C₁ * (C₂ * (1 + L * SV.frak X n' (SV.gcdS (q * r * k) n' / d) k q r))) := by
          apply mul_le_mul_of_nonneg_left _ hw0
          exact le_trans hA (mul_le_mul_of_nonneg_left hI hC₁)
      _ = C₁ * C₂ * d * Psi X L n' (SV.gcdS (q * r * k) n' / d) k q r := by
          unfold Psi
          rw [hgR]
          push_cast
          field_simp

end Principia.Erdos1054.Proofs.SvSmallH

namespace Principia.Erdos1054.Proofs.SvSmallH

open Finset

lemma ratio322_nonneg (X : ℝ) (n n' : ℕ) : 0 ≤ SV.ratio322 X n n' := by
  unfold SV.ratio322
  apply Finset.prod_nonneg
  intro p hp
  rw [Finset.mem_filter] at hp
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp.1).two_le
  apply div_nonneg <;> linarith

/-- `(log X · log log X / (X^{1/20} log Y)) · X^{1/50} ≤ 40000` for large `X`. -/
lemma Wf_bound {X : ℝ} (hXe : Real.exp (120 * Real.exp 3) ≤ X) :
    Real.log X * logIt 2 X / (X ^ ((1 : ℝ) / 20) * Real.log (SV.Ycut X)) *
      X ^ ((1 : ℝ) / 50) ≤ 40000 := by
  obtain ⟨hX1, hlX, _, _, _, _⟩ := bigX_facts hXe
  obtain ⟨hlY1, _, hl2, _, _⟩ := logY_facts hXe
  have hX0 : 0 < X := by linarith
  have hl2X : logIt 2 X ≤ Real.log X := by
    have h1 : logIt 2 X = Real.log (Real.log X) := rfl
    rw [h1]
    have := Real.log_le_sub_one_of_pos (show 0 < Real.log X by linarith)
    linarith
  have h200 : Real.log X ≤ X ^ ((1 : ℝ) / 200) / (1 / 200) :=
    Real.log_le_rpow_div hX0.le (by norm_num)
  have hsq : Real.log X ^ 2 ≤ 40000 * X ^ ((1 : ℝ) / 100) := by
    have e : (X ^ ((1 : ℝ) / 200) / (1 / 200)) ^ 2 = 40000 * X ^ ((1 : ℝ) / 100) := by
      rw [div_pow, ← Real.rpow_natCast, ← Real.rpow_mul hX0.le]
      norm_num
      ring
    calc Real.log X ^ 2 ≤ (X ^ ((1 : ℝ) / 200) / (1 / 200)) ^ 2 :=
          pow_le_pow_left₀ (by linarith) h200 2
      _ = 40000 * X ^ ((1 : ℝ) / 100) := e
  have hX20 : 0 < X ^ ((1 : ℝ) / 20) := Real.rpow_pos_of_pos hX0 _
  have hX50 : 0 < X ^ ((1 : ℝ) / 50) := Real.rpow_pos_of_pos hX0 _
  have hcomb : X ^ ((1 : ℝ) / 100) * X ^ ((1 : ℝ) / 50) ≤ X ^ ((1 : ℝ) / 20) := by
    rw [← Real.rpow_add hX0]
    exact (Real.rpow_le_rpow_left_iff hX1).mpr (by norm_num)
  have hnum : Real.log X * logIt 2 X * X ^ ((1 : ℝ) / 50) ≤
      40000 * (X ^ ((1 : ℝ) / 20) * Real.log (SV.Ycut X)) := by
    calc Real.log X * logIt 2 X * X ^ ((1 : ℝ) / 50)
        ≤ Real.log X ^ 2 * X ^ ((1 : ℝ) / 50) := by
          apply mul_le_mul_of_nonneg_right _ hX50.le
          rw [sq]
          exact mul_le_mul_of_nonneg_left hl2X (by linarith)
      _ ≤ 40000 * X ^ ((1 : ℝ) / 100) * X ^ ((1 : ℝ) / 50) :=
          mul_le_mul_of_nonneg_right hsq hX50.le
      _ ≤ 40000 * X ^ ((1 : ℝ) / 20) := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left hcomb (by norm_num)
      _ ≤ 40000 * (X ^ ((1 : ℝ) / 20) * Real.log (SV.Ycut X)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact le_mul_of_one_le_right hX20.le hlY1
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  exact hnum

/-- **One `n'`** (EP1054.tex lines 1829–1857): the fixed-`n'` part of the regrouped sum is at most
`κ Λ / n'`, given the per-`(n', h, k)` residue-class bound, the `k`-sum `≤ κ`, and the `h`-sum
`≤ Λ`. -/
lemma per_n_bound {X L κ Λ : ℝ} {d n' : ℕ} (hκ : 0 ≤ κ) (β : ℕ → ℝ)
    (hβ : ∀ h, 0 ≤ β h) (hn' : 1 ≤ n')
    (hW : ∀ h ∈ Hset X d n', ∀ k ∈ Kset X d h, ∑ qr ∈ Wset X h n' k,
      (1 / ((qr.1 : ℝ) * (qr.2 : ℝ)) + L * (SV.frak X n' h k qr.1 qr.2 / ((qr.1 : ℝ) * (qr.2 : ℝ))))
        ≤ (h.divisors.card : ℝ) * β h)
    (hK : ∀ h, ∑ k ∈ Kset X d h, (1 : ℝ) / k ≤ κ)
    (hH : ∑ h ∈ Hset X d n', (h : ℝ) * (h.divisors.card : ℝ) * β h ≤ Λ) :
    ∑ h ∈ Hset X d n', ∑ k ∈ Kset X d h, ∑ qr ∈ Wset X h n' k, Psi X L n' h k qr.1 qr.2 ≤
      κ * Λ / n' := by
  have hn0 : (0 : ℝ) < n' := by exact_mod_cast hn'
  calc ∑ h ∈ Hset X d n', ∑ k ∈ Kset X d h, ∑ qr ∈ Wset X h n' k, Psi X L n' h k qr.1 qr.2
      = ∑ h ∈ Hset X d n', ∑ k ∈ Kset X d h, (h : ℝ) / n' * (1 / (k : ℝ)) *
          ∑ qr ∈ Wset X h n' k, (1 / ((qr.1 : ℝ) * (qr.2 : ℝ)) +
            L * (SV.frak X n' h k qr.1 qr.2 / ((qr.1 : ℝ) * (qr.2 : ℝ)))) := by
        apply Finset.sum_congr rfl
        intro h _
        apply Finset.sum_congr rfl
        intro k _
        rw [Finset.mul_sum]
        rfl
    _ ≤ ∑ h ∈ Hset X d n', ∑ k ∈ Kset X d h, (h : ℝ) / n' * (1 / (k : ℝ)) *
          ((h.divisors.card : ℝ) * β h) := by
        apply Finset.sum_le_sum
        intro h hh
        apply Finset.sum_le_sum
        intro k hk
        exact mul_le_mul_of_nonneg_left (hW h hh k hk) (by positivity)
    _ = ∑ h ∈ Hset X d n', (h : ℝ) / n' * ((h.divisors.card : ℝ) * β h) *
          ∑ k ∈ Kset X d h, (1 : ℝ) / k := by
        apply Finset.sum_congr rfl
        intro h _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
    _ ≤ ∑ h ∈ Hset X d n', (h : ℝ) / n' * ((h.divisors.card : ℝ) * β h) * κ := by
        apply Finset.sum_le_sum
        intro h _
        have := hβ h
        exact mul_le_mul_of_nonneg_left (hK h) (by positivity)
    _ = κ / n' * ∑ h ∈ Hset X d n', (h : ℝ) * (h.divisors.card : ℝ) * β h := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro h _
        field_simp
    _ ≤ κ / n' * Λ := mul_le_mul_of_nonneg_left hH (by positivity)
    _ = κ * Λ / n' := by ring


lemma mem_Nset {D : ℕ} {A : Finset ℕ} {X : ℝ} {d n' : ℕ} :
    n' ∈ Nset D A X d ↔ (1 ≤ n' ∧ n' ≤ ⌊X⌋₊) ∧ ∃ p', SV.IsNPart D A X d p' n' := by
  classical
  unfold Nset
  rw [Finset.mem_filter, Finset.mem_Icc]

/-- `W = log X · log log X / (X^{1/20} log Y)`, the size factor of the large-`h` bound of
`eq:sv-qr-sum`. -/
noncomputable def WfX (X : ℝ) : ℝ :=
  Real.log X * logIt 2 X / (X ^ ((1 : ℝ) / 20) * Real.log (SV.Ycut X))

/-- `β(h) = C/h^2 + C W/h`, a common majorant of both cases of `eq:sv-qr-sum`. -/
noncomputable def betaF (C W : ℝ) (h : ℕ) : ℝ := C / (h : ℝ) ^ 2 + C * W / h

lemma WfX_nonneg {X : ℝ} (hXe : Real.exp (120 * Real.exp 3) ≤ X) : 0 ≤ WfX X := by
  obtain ⟨hX1, hlX, _, _, _, _⟩ := bigX_facts hXe
  obtain ⟨hlY1, _, hl2, _, _⟩ := logY_facts hXe
  have hX0 : 0 < X := by linarith
  unfold WfX
  have : 0 < X ^ ((1 : ℝ) / 20) := Real.rpow_pos_of_pos hX0 _
  apply div_nonneg (mul_nonneg (by linarith) (by linarith)) (mul_nonneg this.le (by linarith))

lemma betaF_nonneg {C W : ℝ} (hC : 0 ≤ C) (hW : 0 ≤ W) (h : ℕ) : 0 ≤ betaF C W h := by
  unfold betaF
  positivity

/-- **The residue-class part for one `(n', h, k)`**: `eq:sv-qr-sum` in each of the at most `τ(h)`
residue pairs, with both cases majorised by `β(h)`. -/
lemma W_part {X : ℝ} {d n' : ℕ} (hXe : Real.exp (120 * Real.exp 3) ≤ X)
    {C₃ : ℝ}
    (hQ : ∀ h k a b : ℕ, h ∣ aliquot n' / d → Squarefree h → (h : ℝ) ≤ X ^ ((10 : ℝ) / 33) →
      k ∈ SV.kSet X d → SV.ResiduePair h n' k a b →
      (X ^ ((1 : ℝ) / 20) < (h : ℝ) →
          ∑ q ∈ SV.qClass X h a, ∑ r ∈ SV.rClass X h b,
              (1 / ((q : ℝ) * (r : ℝ)) + logIt 2 X / Real.log (SV.Ycut X) *
                (SV.frak X n' h k q r / ((q : ℝ) * (r : ℝ)))) ≤
            C₃ * (Real.log X * logIt 2 X /
              ((h : ℝ) * X ^ ((1 : ℝ) / 20) * Real.log (SV.Ycut X)))) ∧
        ((h : ℝ) ≤ X ^ ((1 : ℝ) / 20) →
          ∑ q ∈ SV.qClass X h a, ∑ r ∈ SV.rClass X h b,
              (1 / ((q : ℝ) * (r : ℝ)) + logIt 2 X / Real.log (SV.Ycut X) *
                (SV.frak X n' h k q r / ((q : ℝ) * (r : ℝ)))) ≤
            C₃ * (1 / (h : ℝ) ^ 2)))
    (hPC : Claim_SvResiduePairCount) :
    ∀ h ∈ Hset X d n', ∀ k ∈ Kset X d h, ∑ qr ∈ Wset X h n' k,
      (1 / ((qr.1 : ℝ) * (qr.2 : ℝ)) + logIt 2 X / Real.log (SV.Ycut X) *
        (SV.frak X n' h k qr.1 qr.2 / ((qr.1 : ℝ) * (qr.2 : ℝ))))
        ≤ (h.divisors.card : ℝ) * betaF (max C₃ 0) (WfX X) h := by
  obtain ⟨hX1, _, _, _, _, _⟩ := bigX_facts hXe
  obtain ⟨hlY1, _, hl2, _, _⟩ := logY_facts hXe
  have hX0 : 0 < X := by linarith
  have hW0 := WfX_nonneg hXe
  have hC₃0 : 0 ≤ max C₃ 0 := le_max_right _ _
  have hL0 : 0 ≤ logIt 2 X / Real.log (SV.Ycut X) := by positivity
  intro h hh k hk
  unfold Hset at hh
  rw [Finset.mem_filter, Nat.mem_divisors] at hh
  obtain ⟨⟨hhd, _⟩, hsq, hhX⟩ := hh
  unfold Kset at hk
  rw [Finset.mem_filter] at hk
  obtain ⟨hkS, hck, hcsk⟩ := hk
  have hh1 : 1 ≤ h := Nat.pos_of_ne_zero (fun h0 => by subst h0; exact not_squarefree_zero hsq)
  have hh0 : (0 : ℝ) < h := by exact_mod_cast hh1
  apply residue_class_bound hh1
    (fun q r => 1 / ((q : ℝ) * (r : ℝ)) + logIt 2 X / Real.log (SV.Ycut X) *
      (SV.frak X n' h k q r / ((q : ℝ) * (r : ℝ))))
    (fun q r => by
      have := frak_nonneg X n' h k q r
      positivity) (betaF_nonneg hC₃0 hW0 h) _ (hPC h n' k hsq hck hcsk)
  intro a b hab
  obtain ⟨hQ1, hQ2⟩ := hQ h k a b hhd hsq hhX hkS hab
  have hb1 : 0 ≤ max C₃ 0 / (h : ℝ) ^ 2 := by positivity
  have hb2 : 0 ≤ max C₃ 0 * WfX X / h := by positivity
  by_cases hcase : X ^ ((1 : ℝ) / 20) < (h : ℝ)
  · refine le_trans (hQ1 hcase) ?_
    have e : Real.log X * logIt 2 X / ((h : ℝ) * X ^ ((1 : ℝ) / 20) *
        Real.log (SV.Ycut X)) = WfX X / h := by
      unfold WfX
      field_simp
    rw [e]
    unfold betaF
    have h1 : C₃ * (WfX X / h) ≤ max C₃ 0 * WfX X / h := by
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    linarith
  · refine le_trans (hQ2 (not_lt.mp hcase)) ?_
    unfold betaF
    have h1 : C₃ * (1 / (h : ℝ) ^ 2) ≤ max C₃ 0 / (h : ℝ) ^ 2 := by
      rw [mul_one_div]
      exact div_le_div_of_nonneg_right (le_max_left _ _) (by positivity)
    linarith

/-- **The `h`-sum for one `n'`**: `∑_{h ∈ Hset} h τ(h) β(h) ≤ C₃' B^2 + C₃' · 40000 Cε'^2`,
from `∑_{h∣m} τ(h)/h ≤ (σ(m)/m)^2 ≤ B^2`, `∑_{h∣m} τ(h) ≤ τ(m)^2`, the divisor bound with
`ε = 1/200` and `m ≤ X^2`, and `W X^{1/50} ≤ 40000`. -/
lemma H_part {D : ℕ} {B X : ℝ} {A : Finset ℕ} {d n' : ℕ} (hXe : Real.exp (120 * Real.exp 3) ≤ X)
    (hreg : ∀ M ∈ A, SV.RegularMember D B X M) (hd1 : 1 ≤ d) {C₃ Cε : ℝ}
    (hε : ∀ n : ℕ, 1 ≤ n → (n.divisors.card : ℝ) ≤ Cε * (n : ℝ) ^ ((1 : ℝ) / 200))
    (hn' : n' ∈ Nset D A X d) :
    ∑ h ∈ Hset X d n', (h : ℝ) * (h.divisors.card : ℝ) * betaF (max C₃ 0) (WfX X) h ≤
      max C₃ 0 * B ^ 2 + max C₃ 0 * (40000 * (max Cε 0) ^ 2) := by
  classical
  obtain ⟨hX1, _, _, _, _, hXb⟩ := bigX_facts hXe
  have hX0 : 0 < X := by linarith
  have hW0 := WfX_nonneg hXe
  have hC₃0 : 0 ≤ max C₃ 0 := le_max_right _ _
  have hCε0 : 0 ≤ max Cε 0 := le_max_right _ _
  unfold Nset at hn'
  rw [Finset.mem_filter, Finset.mem_Icc] at hn'
  obtain ⟨⟨hn'1, hn'X⟩, p', hN'⟩ := hn'
  obtain ⟨_, _, _, hRn', hab'⟩ := nPart_facts hXb hreg hN'
  obtain ⟨_, _, _, hda', han', _, _, _⟩ := regAt_basic hn'1 hRn'
  have hm1 : 1 ≤ aliquot n' / d := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero han') hda') hd1
  have hmdvd : aliquot n' / d ∣ aliquot n' := Nat.div_dvd_of_dvd hda'
  have hsub : Hset X d n' ⊆ (aliquot n' / d).divisors := by
    intro h hh
    unfold Hset at hh
    exact (Finset.mem_filter.mp hh).1
  have hBm : abundancy (aliquot n' / d) ≤ B :=
    le_trans (abundancy_mono hm1 (Nat.pos_of_ne_zero han') hmdvd) hab'
  have hmX : ((aliquot n' / d : ℕ) : ℝ) ≤ X ^ 2 := by
    have h1 : aliquot n' / d ≤ n' ^ 2 := le_trans (Nat.div_le_self _ _)
      (le_trans (Nat.sub_le _ _) (sig_le_sq n'))
    have h2 : (n' : ℝ) ≤ X := le_trans (Nat.cast_le.mpr hn'X) (Nat.floor_le hX0.le)
    calc ((aliquot n' / d : ℕ) : ℝ) ≤ ((n' ^ 2 : ℕ) : ℝ) := by exact_mod_cast h1
      _ = (n' : ℝ) ^ 2 := by push_cast; ring
      _ ≤ X ^ 2 := pow_le_pow_left₀ (by positivity) h2 2
  have hτm : ((aliquot n' / d).divisors.card : ℝ) ≤ max Cε 0 * X ^ ((1 : ℝ) / 100) := by
    have h1 := hε _ hm1
    have h2 : ((aliquot n' / d : ℕ) : ℝ) ^ ((1 : ℝ) / 200) ≤ X ^ ((1 : ℝ) / 100) := by
      calc ((aliquot n' / d : ℕ) : ℝ) ^ ((1 : ℝ) / 200) ≤ (X ^ 2) ^ ((1 : ℝ) / 200) :=
            Real.rpow_le_rpow (by positivity) hmX (by norm_num)
        _ = X ^ ((1 : ℝ) / 100) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hX0.le]
            norm_num
    calc ((aliquot n' / d).divisors.card : ℝ)
        ≤ Cε * ((aliquot n' / d : ℕ) : ℝ) ^ ((1 : ℝ) / 200) := h1
      _ ≤ max Cε 0 * ((aliquot n' / d : ℕ) : ℝ) ^ ((1 : ℝ) / 200) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ max Cε 0 * X ^ ((1 : ℝ) / 100) := mul_le_mul_of_nonneg_left h2 hCε0
  have hhs := h_sum_bound hm1 _ hsub hBm hC₃0 hW0 hτm
  have hWT : WfX X * (max Cε 0 * X ^ ((1 : ℝ) / 100)) ^ 2 ≤ 40000 * (max Cε 0) ^ 2 := by
    have e1 : (X ^ ((1 : ℝ) / 100)) ^ 2 = X ^ ((1 : ℝ) / 50) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hX0.le]
      norm_num
    have e : WfX X * (max Cε 0 * X ^ ((1 : ℝ) / 100)) ^ 2 =
        (max Cε 0) ^ 2 * (WfX X * X ^ ((1 : ℝ) / 50)) := by
      rw [mul_pow, e1]
      ring
    rw [e]
    have hb : WfX X * X ^ ((1 : ℝ) / 50) ≤ 40000 := Wf_bound hXe
    calc (max Cε 0) ^ 2 * (WfX X * X ^ ((1 : ℝ) / 50)) ≤ (max Cε 0) ^ 2 * 40000 :=
          mul_le_mul_of_nonneg_left hb (sq_nonneg _)
      _ = 40000 * (max Cε 0) ^ 2 := by ring
  have hfin : max C₃ 0 * WfX X * (max Cε 0 * X ^ ((1 : ℝ) / 100)) ^ 2 ≤
      max C₃ 0 * (40000 * (max Cε 0) ^ 2) := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hWT hC₃0
  calc ∑ h ∈ Hset X d n', (h : ℝ) * (h.divisors.card : ℝ) * betaF (max C₃ 0) (WfX X) h
      ≤ max C₃ 0 * B ^ 2 + max C₃ 0 * WfX X * (max Cε 0 * X ^ ((1 : ℝ) / 100)) ^ 2 := hhs
    _ ≤ max C₃ 0 * B ^ 2 + max C₃ 0 * (40000 * (max Cε 0) ^ 2) := by linarith

end Principia.Erdos1054.Proofs.SvSmallH

namespace Principia.Erdos1054.Proofs

open Finset

theorem link_Claim_SvSmallH : Principia.Erdos1054.Spine.Link_Claim_SvSmallH := by
  intro hA322 hSqf hRes hPC hIT hQR hKR hMR hDiv δ hδ hδ1 D hD 𝒜 hfam c c₁ c₂ c₃ hc _ _ _
  obtain ⟨C₁, X₁a, hA⟩ := hA322 δ hδ hδ1 D hD 𝒜 hfam
  obtain ⟨X₁s, hS⟩ := hSqf δ hδ hδ1 D hD 𝒜 hfam
  obtain ⟨X₁r, hR⟩ := hRes δ hδ hδ1 D hD 𝒜 hfam
  obtain ⟨C₂, X₁i, hI⟩ := hIT δ hδ hδ1 D hD 𝒜 hfam
  obtain ⟨C₃, X₁q, hQ⟩ := hQR δ hδ hδ1 D hD 𝒜 hfam
  obtain ⟨CK, hK⟩ := hKR
  obtain ⟨XK, hK'⟩ := hK c hc
  obtain ⟨CM, hM⟩ := hMR
  obtain ⟨XM, hM'⟩ := hM c hc
  obtain ⟨Cε, hε⟩ := hDiv (1 / 200) (by norm_num)
  obtain ⟨_, _, B, hB, X₁, hX₁⟩ := hfam
  have hC₁0 : 0 ≤ max C₁ 0 := le_max_right _ _
  have hC₂0 : 0 ≤ max C₂ 0 := le_max_right _ _
  have hC₃0 : 0 ≤ max C₃ 0 := le_max_right _ _
  have hCK0 : 0 ≤ max CK 0 := le_max_right _ _
  have hCM0 : 0 ≤ max CM 0 := le_max_right _ _
  have hCε0 : 0 ≤ max Cε 0 := le_max_right _ _
  set Λ : ℝ := max C₃ 0 * B ^ 2 + max C₃ 0 * (40000 * (max Cε 0) ^ 2) with hΛ
  have hΛ0 : 0 ≤ Λ := by positivity
  refine ⟨max C₁ 0 * max C₂ 0 * max CK 0 * max CM 0 * Λ,
    max (max (max X₁ X₁a) (max X₁s X₁r)) (max (max X₁i X₁q) (max (max XK XM)
      (Real.exp (120 * Real.exp 3)))), ?_⟩
  intro X hX 𝒟 hcl d hd
  have hX' := hX
  simp only [ge_iff_le, max_le_iff] at hX'
  obtain ⟨⟨⟨hXa, hXA⟩, ⟨hXS, hXR⟩⟩, ⟨⟨hXI, hXQ⟩, ⟨⟨hXK, hXM⟩, hXe⟩⟩⟩ := hX'
  obtain ⟨hX1, hlX, _, _, _, hXb⟩ := SvSmallH.bigX_facts hXe
  obtain ⟨hlY1, _, hl2, _, _⟩ := SvSmallH.logY_facts hXe
  have hX0 : 0 < X := by linarith
  have hlX0 : 0 < Real.log X := by linarith
  obtain ⟨_, _, hreg⟩ := hX₁ X hXa
  obtain ⟨hd1, hdsm, hdc⟩ := hcl.1 d hd
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
  have hL0 : 0 ≤ logIt 2 X / Real.log (SV.Ycut X) := by positivity
  set κ : ℝ := max CK 0 * (Real.log X / ((d : ℝ) * Real.log (SV.Ycut X))) with hκ
  set μ : ℝ := max CM 0 * (Real.log X / ((d : ℝ) * Real.log (SV.Ycut X))) with hμ
  have hκ0 : 0 ≤ κ := by rw [hκ]; positivity
  have hμ0 : 0 ≤ μ := by rw [hμ]; positivity
  -- (a) the regrouping
  have hreg1 := SvSmallH.pair_regroup (L := logIt 2 X / Real.log (SV.Ycut X)) hXb hreg hC₁0
    hC₂0 hL0
    (fun n n' hC hH => le_trans (hA X hXA d n n' hC hH)
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (SvSmallH.ratio322_nonneg X n n')))
    (fun n n' hC hH => hS X hXS d n n' hC hH)
    (fun p q r k n' hm hC hH => hR X hXR d p q r k n' hm hC hH)
    (fun p q r k n' hm hC hH => le_trans (hI X hXI d p q r k n' hm hC hH)
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by
        have := SvSmallH.frak_nonneg X n' (SV.gcdS (q * r * k) n' / d) k q r
        positivity)))
  -- (b) one `n'` at a time
  have hKsum : ∀ h, ∑ k ∈ SvSmallH.Kset X d h, (1 : ℝ) / k ≤ κ := by
    intro h
    calc ∑ k ∈ SvSmallH.Kset X d h, (1 : ℝ) / k ≤ ∑ k ∈ SV.kSet X d, (1 : ℝ) / k := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          intro i _ _
          positivity
      _ ≤ CK * (Real.log X / ((d : ℝ) * Real.log (SV.Ycut X))) := hK' X hXK d hd1 hdsm hdc
      _ ≤ κ := by
          rw [hκ]
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  have hper : ∀ n' ∈ SvSmallH.Nset D (𝒜 X) X d,
      ∑ h ∈ SvSmallH.Hset X d n', ∑ k ∈ SvSmallH.Kset X d h,
        ∑ qr ∈ SvSmallH.Wset X h n' k,
          SvSmallH.Psi X (logIt 2 X / Real.log (SV.Ycut X)) n' h k qr.1 qr.2 ≤ κ * Λ / n' := by
    intro n' hn'
    obtain ⟨⟨hn'1, _⟩, hnp⟩ := SvSmallH.mem_Nset.mp hn'
    exact SvSmallH.per_n_bound hκ0 _ (SvSmallH.betaF_nonneg hC₃0 (SvSmallH.WfX_nonneg hXe))
      hn'1
      (SvSmallH.W_part hXe (fun h k a b hhd hsq hhX hkS hab =>
        hQ X hXQ d n' h k a b hnp hhd hsq hhX hkS hab) hPC)
      hKsum (SvSmallH.H_part hXe hreg hd1 hε hn')
  -- (c) the `n'`-sum
  have hNsum : ∑ n' ∈ SvSmallH.Nset D (𝒜 X) X d, (1 : ℝ) / n' ≤ μ := by
    calc ∑ n' ∈ SvSmallH.Nset D (𝒜 X) X d, (1 : ℝ) / n' ≤ _ := SvSmallH.Nset_recip hreg d
      _ ≤ CM * (Real.log X / ((d : ℝ) * Real.log (SV.Ycut X))) := hM' X hXM d hd1 hdsm hdc
      _ ≤ μ := by
          rw [hμ]
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  have hΦ : ∑ n' ∈ SvSmallH.Nset D (𝒜 X) X d, ∑ h ∈ SvSmallH.Hset X d n',
      ∑ k ∈ SvSmallH.Kset X d h, ∑ qr ∈ SvSmallH.Wset X h n' k,
        SvSmallH.Psi X (logIt 2 X / Real.log (SV.Ycut X)) n' h k qr.1 qr.2 ≤ κ * Λ * μ := by
    calc ∑ n' ∈ SvSmallH.Nset D (𝒜 X) X d, ∑ h ∈ SvSmallH.Hset X d n',
          ∑ k ∈ SvSmallH.Kset X d h, ∑ qr ∈ SvSmallH.Wset X h n' k,
            SvSmallH.Psi X (logIt 2 X / Real.log (SV.Ycut X)) n' h k qr.1 qr.2
        ≤ ∑ n' ∈ SvSmallH.Nset D (𝒜 X) X d, κ * Λ / n' := Finset.sum_le_sum hper
      _ = κ * Λ * ∑ n' ∈ SvSmallH.Nset D (𝒜 X) X d, (1 : ℝ) / n' := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro n' _
          ring
      _ ≤ κ * Λ * μ := mul_le_mul_of_nonneg_left hNsum (by positivity)
  -- (d) assemble
  have hpre : 0 ≤ X * Real.log (SV.Ycut X) / Real.log X ^ 2 := by positivity
  calc X * Real.log (SV.Ycut X) / Real.log X ^ 2 *
        SV.reducedCollisionSum D (𝒜 X) X d (fun h => (h : ℝ) ≤ X ^ ((10 : ℝ) / 33))
      ≤ X * Real.log (SV.Ycut X) / Real.log X ^ 2 *
          (max C₁ 0 * max C₂ 0 * d * ∑ n' ∈ SvSmallH.Nset D (𝒜 X) X d,
            ∑ h ∈ SvSmallH.Hset X d n', ∑ k ∈ SvSmallH.Kset X d h,
              ∑ qr ∈ SvSmallH.Wset X h n' k,
                SvSmallH.Psi X (logIt 2 X / Real.log (SV.Ycut X)) n' h k qr.1 qr.2) :=
        mul_le_mul_of_nonneg_left hreg1 hpre
    _ ≤ X * Real.log (SV.Ycut X) / Real.log X ^ 2 *
          (max C₁ 0 * max C₂ 0 * d * (κ * Λ * μ)) := by
        apply mul_le_mul_of_nonneg_left _ hpre
        exact mul_le_mul_of_nonneg_left hΦ (by positivity)
    _ = max C₁ 0 * max C₂ 0 * max CK 0 * max CM 0 * Λ *
          (X / ((d : ℝ) * Real.log (SV.Ycut X))) := by
        rw [hκ, hμ]
        field_simp

end Principia.Erdos1054.Proofs
