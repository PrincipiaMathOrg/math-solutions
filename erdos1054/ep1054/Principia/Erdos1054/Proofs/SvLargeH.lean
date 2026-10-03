/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Erdos1054.Spine
import Mathlib.NumberTheory.FactorisationProperties
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Squarefree
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false

/-!
# EP1054 `prop:sv-second-moment`, off-diagonal collisions: the `SvLargeH` package of the spine

Discharges the eleven obligations of `Principia.Erdos1054.Spine` for EP1054.tex lines 1542–1739
(`Campaigns/Erdos-1054/collab-paper/EP1054.tex`): the collision equation, the linear Diophantine
parametrization with the two-dimensional sieve, the totient ratios, the reduction of the `A_3`
factor, and the large-`h` rigidity argument.

Leaf (proved from the definitions and Mathlib alone):
* `leaf_Eq_SvCollision` (lines 1562–1566) — `s(pn) = p s(n) + σ(n)` for a prime `p ∤ n`
  (multiplicativity of `σ`).

Links (proved from exactly the dependencies the spine names, the regular-family hypothesis of the
statements, and the leaf above):
* `link_Eq_SvTotient` (1620–1627) — `Std_totient_sigma` and Mathlib's
  `Nat.abundancyIndex_le_of_dvd`.
* `link_Claim_SvSigmaDistinct` (1572–1580) — `p > X^{8/15}/2 > C_δ X^{7/15} > s(n')` forces
  `p = p'`, then `n = n'`.
* `link_Claim_SvSievePairs` (1588–1618) — from one collision `(p₀, p'₀)` every other one is
  `p = p₀ + A₂t`, `p' = p'₀ + A₁t` (`lin_param`); the `t` lie in an interval of length
  `T = X/(2nA₂) ∈ [X^{1/30}, Xg/(nn')]` (`sieve_T_bounds`); the determinant is `±A₃ ≠ 0`; then
  `Cite_LP_sieve37` and `log T ≥ (log X)/30` (`sieve_final`).
* `link_Claim_SvA3Reduction` (1631–1646) — `m/φ(m) = ∏_{p∣m} p/(p−1)` (`phiRatio_eq_prod`) split
  into four prime ranges (`phiRatio_split`): primes `≤ (log log X)²` give `≤ 1/Δ ≤ 16 e^γ log Y`
  (`Std_Mertens3`, `invDelta_bound`, `logIt3_le_logY`); primes of `σ(n)` above `(log log X)²`
  give `≤ e²` (`eq:sv-LP25`); primes above `log X` give `≤ e²` (`A₃ ≤ X`); the rest is `A'_{3,2}`.
  The constant is absolute, `16 e^γ e⁴`.
* `link_Claim_SvLargeHUnits` (1663–1676), `link_Eq_SvLargeHCongruence` (1677–1684),
  `link_Claim_SvLargeHRigidity` (1663–1708) — `units_core`, `congr_core` (elimination of `q, q'`),
  and `rigid_core` (the reduced-denominator argument: `gcd(s(ℓ)/d, ℓ²/d) = 1` from the maximality
  of the smooth part, `reg_coprime_sq`).
* `link_Claim_SvLargeH` (1710–1731) — every large-`h` pair is `(qℓ, q'ℓ)` for a quadruple
  `(q', ℓ, h, q)` of a bounding box (`lh_cover`); the box sum of `dh log X/(qq'ℓ²)` is
  `≤ 2C d log X · X^{1/120+1/60−3/40} (1+log X)²` (`lh_nested`: `h·#{q ≡ q' (h)} ≤ 2X^{11/30}`,
  `τ(s(q'ℓ)) ≤ C X^{1/120}`, `∑ℓ^{-2}[ℓ > X^{3/40}] ≤ X^{-3/40}(1+log X)`); `A'_{3,2}/φ ≤ log X`
  (`ratio32_le_log`, telescoping `∏_{2≤m≤M} m/(m−1) = M`) suffices, so `Std_Mertens2` is not used.
* `link_Claim_SvA322Reduction` (1733–1739) — the removed primes form `v ∣ s(n')`, and
  `v/φ(v) ≤ ζ(2) σ(s(n'))/s(n') ≤ ζ(2)B` (`Eq_SvTotient`, `eq:sv-image-abundancy`).
* `link_Eq_SvReducedCollisionSum` (1647–1657) — the sum splits additively at `h = X^{10/33}`.
-/

namespace Principia.Erdos1054.Proofs.SvLargeH

open Finset

theorem le_sig (n : ℕ) : n ≤ sig n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Nat.zero_le _
  · show n ≤ ArithmeticFunction.sigma 1 n
    rw [ArithmeticFunction.sigma_one_apply]
    exact Finset.single_le_sum (f := fun d : ℕ => d) (fun _ _ => Nat.zero_le _)
      (Nat.mem_divisors_self n hn.ne')

theorem sig_eq_aliquot_add (n : ℕ) : sig n = aliquot n + n := by
  have := le_sig n
  show sig n = (sig n - n) + n
  omega

theorem sig_prime_mul (p n : ℕ) (hp : p.Prime) (hpn : ¬ p ∣ n) :
    sig (p * n) = (p + 1) * sig n := by
  have hcop : Nat.Coprime p n := (Nat.Prime.coprime_iff_not_dvd hp).2 hpn
  show ArithmeticFunction.sigma 1 (p * n) = (p + 1) * ArithmeticFunction.sigma 1 n
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop]
  congr 1
  have h1 := ArithmeticFunction.sigma_one_apply_prime_pow (i := 1) hp
  rw [pow_one] at h1
  rw [h1, Finset.sum_range_succ, Finset.sum_range_one, pow_zero, pow_one, add_comm]

theorem aliquot_prime_mul (p n : ℕ) (hp : p.Prime) (hpn : ¬ p ∣ n) :
    aliquot (p * n) = p * aliquot n + sig n := by
  have h1 := sig_prime_mul p n hp hpn
  have h2 := sig_eq_aliquot_add n
  show sig (p * n) - p * n = p * aliquot n + sig n
  rw [h1, h2]
  apply Nat.sub_eq_of_eq_add
  ring

/-- `eq:sv-collision` (leaf). -/
theorem collision : Eq_SvCollision := fun p n hp hpn => aliquot_prime_mul p n hp hpn

theorem abundancy_eq_cast (n : ℕ) : abundancy n = ((n.abundancyIndex : ℚ) : ℝ) := by
  unfold abundancy Nat.abundancyIndex
  show ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) / n = _
  rw [ArithmeticFunction.sigma_one_apply]
  push_cast
  rfl

theorem abundancy_le_of_dvd {v m : ℕ} (hm : m ≠ 0) (h : v ∣ m) : abundancy v ≤ abundancy m := by
  rw [abundancy_eq_cast, abundancy_eq_cast]
  exact_mod_cast Nat.abundancyIndex_le_of_dvd hm h

theorem totient_link : Spine.Link_Eq_SvTotient := by
  intro hts v m hv hm hvm
  refine ⟨?_, abundancy_le_of_dvd (by omega) hvm⟩
  have := hts v hv
  unfold abundancy
  exact this

/-! ## smooth parts -/

theorem isSmooth_one (y : ℝ) : IsSmooth y 1 := by
  intro p hp
  simp at hp

theorem smoothPart_zero (y : ℝ) : SV.smoothPart y 0 = 0 := by
  simp [SV.smoothPart]

open Classical in
theorem smoothPart_mem (y : ℝ) {m : ℕ} (hm : m ≠ 0) :
    SV.smoothPart y m ∈ m.divisors.filter (fun d => IsSmooth y d) := by
  have hne : (m.divisors.filter (fun d => IsSmooth y d)).Nonempty :=
    ⟨1, Finset.mem_filter.2 ⟨Nat.one_mem_divisors.2 hm, isSmooth_one y⟩⟩
  obtain ⟨i, hi, heq⟩ := Finset.exists_mem_eq_sup _ hne id
  unfold SV.smoothPart
  rw [heq]
  exact hi

open Classical in
theorem le_smoothPart (y : ℝ) {m e : ℕ} (he : e ∣ m) (hm : m ≠ 0) (hs : IsSmooth y e) :
    e ≤ SV.smoothPart y m := by
  unfold SV.smoothPart
  have : e ∈ m.divisors.filter (fun d => IsSmooth y d) :=
    Finset.mem_filter.2 ⟨Nat.mem_divisors.2 ⟨he, hm⟩, hs⟩
  exact Finset.le_sup (f := id) this

open Classical in
theorem smoothPart_isSmooth (y : ℝ) {m : ℕ} (hm : m ≠ 0) : IsSmooth y (SV.smoothPart y m) :=
  (Finset.mem_filter.1 (smoothPart_mem y hm)).2

open Classical in
theorem smoothPart_dvd (y : ℝ) {m : ℕ} (hm : m ≠ 0) : SV.smoothPart y m ∣ m :=
  (Nat.mem_divisors.1 (Finset.mem_filter.1 (smoothPart_mem y hm)).1).1

/-- The maximality of the smooth part: no prime `q ≤ y` has `q * d ∣ m`. -/
theorem not_prime_mul_smoothPart_dvd (y : ℝ) {m q : ℕ} (hm : m ≠ 0) (hq : q.Prime)
    (hqy : (q : ℝ) ≤ y) (hdvd : q * SV.smoothPart y m ∣ m) : False := by
  have hdm := smoothPart_dvd y hm
  have hsm := smoothPart_isSmooth y hm
  have hd0 : SV.smoothPart y m ≠ 0 := by
    rintro h0; rw [h0] at hdm; exact hm (Nat.eq_zero_of_zero_dvd hdm)
  have hsm' : IsSmooth y (q * SV.smoothPart y m) := by
    intro p hp
    rw [Nat.primeFactors_mul hq.ne_zero hd0, Finset.mem_union] at hp
    rcases hp with hp | hp
    · rw [hq.primeFactors, Finset.mem_singleton] at hp
      rw [hp]; exact hqy
    · exact hsm p hp
  have := le_smoothPart y hdvd hm hsm'
  have h2 := hq.two_le
  have : 2 * SV.smoothPart y m ≤ SV.smoothPart y m :=
    le_trans (Nat.mul_le_mul_right _ h2) this
  omega

/-- A prime dividing a `y`-smooth nonzero number is `≤ y`. -/
theorem prime_le_of_dvd_smooth {y : ℝ} {d q : ℕ} (hd : d ≠ 0) (hs : IsSmooth y d) (hq : q.Prime)
    (hqd : q ∣ d) : (q : ℝ) ≤ y :=
  hs q (Nat.mem_primeFactors.2 ⟨hq, hqd, hd⟩)


/-! ## Real-power helpers -/

theorem le_rpow_inv {a X : ℝ} {n : ℕ} (hn : 0 < n) (ha : 0 ≤ a) (h : a ^ n ≤ X) :
    a ≤ X ^ ((1 : ℝ) / n) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  calc a = (a ^ n) ^ ((1 : ℝ) / n) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul ha, mul_one_div_cancel hn', Real.rpow_one]
    _ ≤ X ^ ((1 : ℝ) / n) := Real.rpow_le_rpow (pow_nonneg ha n) h (by positivity)

theorem rpow_mul_rpow {X : ℝ} (hX : 0 < X) (a b : ℝ) : X ^ a * X ^ b = X ^ (a + b) :=
  (Real.rpow_add hX a b).symm

/-! ## Tuple arithmetic -/

section tuple

variable {D : ℕ} {X : ℝ} {p q r k : ℕ}

theorem tuple_k_pos (hX : 0 ≤ X) (ht : S4a.A0Tuple D X p q r k) : 0 < k := by
  obtain ⟨-, -, -, -, hk1, -⟩ := ht
  have : (0 : ℝ) < k := lt_of_le_of_lt (Real.rpow_nonneg hX _) hk1
  exact_mod_cast this

theorem tuple_l_le (hX : 1 ≤ X) (ht : S4a.A0Tuple D X p q r k) :
    ((r * k : ℕ) : ℝ) ≤ X ^ ((1 : ℝ) / 10) := by
  obtain ⟨-, -, -, -, hk1, hk2, hr1, hr2, -⟩ := ht
  have hX0 : 0 < X := by linarith
  push_cast
  calc (r : ℝ) * k ≤ X ^ ((1 : ℝ) / 12) * X ^ ((1 : ℝ) / 60) :=
        mul_le_mul hr2 hk2 (Nat.cast_nonneg _) (Real.rpow_nonneg hX0.le _)
    _ = X ^ ((1 : ℝ) / 10) := by rw [rpow_mul_rpow hX0]; norm_num

theorem tuple_l_gt (hX : 1 ≤ X) (ht : S4a.A0Tuple D X p q r k) :
    X ^ ((3 : ℝ) / 40) < ((r * k : ℕ) : ℝ) := by
  obtain ⟨-, -, -, -, hk1, hk2, hr1, hr2, -⟩ := ht
  have hX0 : 0 < X := by linarith
  push_cast
  calc X ^ ((3 : ℝ) / 40) = X ^ ((1 : ℝ) / 15) * X ^ ((1 : ℝ) / 120) := by
        rw [rpow_mul_rpow hX0]; norm_num
    _ < (r : ℝ) * k := mul_lt_mul'' hr1 hk1 (Real.rpow_nonneg hX0.le _) (Real.rpow_nonneg hX0.le _)

theorem tuple_n_le (hX : 1 ≤ X) (ht : S4a.A0Tuple D X p q r k) :
    ((q * r * k : ℕ) : ℝ) ≤ X ^ ((7 : ℝ) / 15) := by
  have hl := tuple_l_le hX ht
  obtain ⟨-, -, -, -, -, -, -, -, hq1, hq2, -⟩ := ht
  have hX0 : 0 < X := by linarith
  have : ((q * r * k : ℕ) : ℝ) = (q : ℝ) * ((r * k : ℕ) : ℝ) := by push_cast; ring
  rw [this]
  calc (q : ℝ) * ((r * k : ℕ) : ℝ) ≤ X ^ ((11 : ℝ) / 30) * X ^ ((1 : ℝ) / 10) :=
        mul_le_mul hq2 hl (Nat.cast_nonneg _) (Real.rpow_nonneg hX0.le _)
    _ = X ^ ((7 : ℝ) / 15) := by rw [rpow_mul_rpow hX0]; norm_num

theorem tuple_q_gt (ht : S4a.A0Tuple D X p q r k) : X ^ ((7 : ℝ) / 20) < (q : ℝ) := by
  obtain ⟨-, -, -, -, -, -, -, -, hq1, -⟩ := ht
  exact hq1

theorem tuple_q_le (ht : S4a.A0Tuple D X p q r k) : (q : ℝ) ≤ X ^ ((11 : ℝ) / 30) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hq2, -⟩ := ht
  exact hq2

theorem tuple_l_lt_q (hX : 1 ≤ X) (ht : S4a.A0Tuple D X p q r k) : r * k < q := by
  have hl := tuple_l_le hX ht
  have hq := tuple_q_gt ht
  have : X ^ ((1 : ℝ) / 10) ≤ X ^ ((7 : ℝ) / 20) :=
    Real.rpow_le_rpow_of_exponent_le hX (by norm_num)
  have : ((r * k : ℕ) : ℝ) < (q : ℝ) := by linarith
  exact_mod_cast this

theorem tuple_n_pos (hX : 1 ≤ X) (ht : S4a.A0Tuple D X p q r k) : 0 < q * r * k := by
  have hk := tuple_k_pos (by linarith) ht
  obtain ⟨-, hq, hr, -⟩ := ht
  exact Nat.mul_pos (Nat.mul_pos hq.pos hr.pos) hk

/-- `p > X^{8/15}/2`. -/
theorem tuple_p_gt (hX : 1 ≤ X) (ht : S4a.A0Tuple D X p q r k) :
    X ^ ((8 : ℝ) / 15) / 2 < (p : ℝ) := by
  have hn := tuple_n_le hX ht
  have hnpos : (0 : ℝ) < ((q * r * k : ℕ) : ℝ) := by exact_mod_cast tuple_n_pos hX ht
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hp1, -⟩ := ht
  have hX0 : 0 < X := by linarith
  have e : (2 * (q : ℝ) * r * k) = 2 * ((q * r * k : ℕ) : ℝ) := by push_cast; ring
  rw [e] at hp1
  have h7 : 0 < X ^ ((7 : ℝ) / 15) := Real.rpow_pos_of_pos hX0 _
  have hX' : X ^ ((8 : ℝ) / 15) * X ^ ((7 : ℝ) / 15) = X := by
    rw [rpow_mul_rpow hX0]; norm_num
  calc X ^ ((8 : ℝ) / 15) / 2 = X / (2 * X ^ ((7 : ℝ) / 15)) := by
        rw [eq_div_iff (by positivity)]
        linear_combination hX'
    _ ≤ X / (2 * ((q * r * k : ℕ) : ℝ)) := by
        apply div_le_div_of_nonneg_left hX0.le (by positivity)
        linarith
    _ < p := hp1

/-- For `X^{1/15} ≥ 2C`, the prime `p` of a tuple exceeds `C · m` for every `m ≤ X^{7/15}`. -/
theorem tuple_p_gt_mul (hX : 1 ≤ X) (ht : S4a.A0Tuple D X p q r k) {C m : ℝ} (hC : 0 ≤ C)
    (hm : m ≤ X ^ ((7 : ℝ) / 15)) (hXC : 2 * C ≤ X ^ ((1 : ℝ) / 15)) : C * m < p := by
  have hp := tuple_p_gt hX ht
  have hX0 : 0 < X := by linarith
  have h8 : X ^ ((8 : ℝ) / 15) = X ^ ((1 : ℝ) / 15) * X ^ ((7 : ℝ) / 15) := by
    rw [rpow_mul_rpow hX0]; norm_num
  have h7 : 0 ≤ X ^ ((7 : ℝ) / 15) := Real.rpow_nonneg hX0.le _
  calc C * m ≤ C * X ^ ((7 : ℝ) / 15) := mul_le_mul_of_nonneg_left hm hC
    _ ≤ X ^ ((8 : ℝ) / 15) / 2 := by
        rw [h8]
        nlinarith
    _ < p := hp

theorem tuple_n_lt_p (hX : 2 ^ 15 ≤ X) (ht : S4a.A0Tuple D X p q r k) : q * r * k < p := by
  have hX1 : 1 ≤ X := by linarith
  have h2 : (2 : ℝ) ≤ X ^ ((1 : ℝ) / 15) := by
    have := le_rpow_inv (n := 15) (by norm_num) (by norm_num : (0 : ℝ) ≤ 2) (by linarith)
    simpa using this
  have := tuple_p_gt_mul hX1 ht (C := 1) (m := ((q * r * k : ℕ) : ℝ)) zero_le_one
    (tuple_n_le hX1 ht) (by linarith)
  rw [one_mul] at this
  exact_mod_cast this

theorem tuple_p_not_dvd (hX : 2 ^ 15 ≤ X) (ht : S4a.A0Tuple D X p q r k) : ¬ p ∣ q * r * k :=
  Nat.not_dvd_of_pos_of_lt (tuple_n_pos (by linarith) ht) (tuple_n_lt_p hX ht)

theorem tuple_q_not_dvd (hX : 1 ≤ X) (ht : S4a.A0Tuple D X p q r k) : ¬ q ∣ r * k := by
  have hk := tuple_k_pos (by linarith) ht
  have hl := tuple_l_lt_q hX ht
  obtain ⟨-, -, hr, -⟩ := ht
  exact Nat.not_dvd_of_pos_of_lt (Nat.mul_pos hr.pos hk) hl

end tuple

/-! ## Regularity consequences -/

section reg

variable {Y : ℝ} {d t : ℕ}

theorem member_reg {D : ℕ} {A : Finset ℕ} {B X : ℝ} (hA : ∀ M ∈ A, SV.RegularMember D B X M)
    {d p q r k : ℕ} (ht : SV.MemberTuple D A X d p q r k) :
    SV.RegularAt (SV.Ycut X) d k ∧ SV.RegularAt (SV.Ycut X) d (r * k) ∧
      SV.RegularAt (SV.Ycut X) d (q * r * k) ∧ SV.RegularAt (SV.Ycut X) d (p * q * r * k) ∧
      SV.SqExcl (q * r * k) ∧ Eq_SvLP25 X (q * r * k) ∧ Eq_SvImageAbundancy B (q * r * k) := by
  obtain ⟨hT, hmem, hd⟩ := ht
  have := hA _ hmem p q r k hT rfl
  rw [hd] at this
  exact this

theorem reg_d_ne (hR : SV.RegularAt Y d t) (ht : t ≠ 0) : d ≠ 0 := by
  rw [hR.1]
  exact (Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero ht)).ne'

theorem reg_d_dvd (hR : SV.RegularAt Y d t) : d ∣ t := by
  rw [hR.1]; exact Nat.gcd_dvd_left _ _

theorem reg_d_dvd_sig (hR : SV.RegularAt Y d t) : d ∣ sig t := by
  rw [hR.1]; exact Nat.gcd_dvd_right _ _

theorem reg_d_dvd_aliquot (hR : SV.RegularAt Y d t) : d ∣ aliquot t :=
  Nat.dvd_sub (reg_d_dvd_sig hR) (reg_d_dvd hR)

theorem reg_aliquot_ne (hR : SV.RegularAt Y d t) (ht : t ≠ 0) : aliquot t ≠ 0 := by
  intro h0
  have h1 := hR.2.2.1
  rw [h0, smoothPart_zero] at h1
  exact reg_d_ne hR ht h1

theorem reg_smooth (hR : SV.RegularAt Y d t) (ht : t ≠ 0) : IsSmooth Y d := by
  rw [hR.2.2.1]
  exact smoothPart_isSmooth Y (reg_aliquot_ne hR ht)

theorem reg_prime_le (hR : SV.RegularAt Y d t) (ht : t ≠ 0) {q : ℕ} (hq : q.Prime) (hqd : q ∣ d) :
    (q : ℝ) ≤ Y :=
  prime_le_of_dvd_smooth (reg_d_ne hR ht) (reg_smooth hR ht) hq hqd

theorem reg_max (hR : SV.RegularAt Y d t) (ht : t ≠ 0) {q : ℕ} (hq : q.Prime)
    (h : q * d ∣ aliquot t) : Y < q := by
  by_contra hle0
  have hle : (q : ℝ) ≤ Y := not_lt.mp hle0
  have h' : q * SV.smoothPart Y (aliquot t) ∣ aliquot t := by rw [← hR.2.2.1]; exact h
  exact not_prime_mul_smoothPart_dvd Y (reg_aliquot_ne hR ht) hq hle h'

theorem reg_coprime (hR : SV.RegularAt Y d t) (ht : t ≠ 0) : Nat.Coprime d (aliquot t / d) := by
  apply Nat.coprime_of_dvd
  intro q hq hqd hqs
  have h1 := reg_prime_le hR ht hq hqd
  have h2 := reg_max hR ht hq (by
    have := Nat.mul_dvd_of_dvd_div (reg_d_dvd_aliquot hR) hqs
    rwa [mul_comm] at this)
  linarith

/-- `gcd(s(t)/d, t²/d) = 1` (the paper's `gcd(ℓ², s(ℓ)) = d`). -/
theorem reg_coprime_sq (hR : SV.RegularAt Y d t) (ht : t ≠ 0) :
    Nat.Coprime (aliquot t / d) (t ^ 2 / d) := by
  apply Nat.coprime_of_dvd
  intro q hq hqs hql
  have h1 : Y < q := reg_max hR ht hq (by
    have := Nat.mul_dvd_of_dvd_div (reg_d_dvd_aliquot hR) hqs
    rwa [mul_comm] at this)
  have hdl : d ∣ t ^ 2 := dvd_pow (reg_d_dvd hR) two_ne_zero
  have hqt : q ∣ t := hq.dvd_of_dvd_pow (dvd_trans hql (Nat.div_dvd_of_dvd hdl))
  have hqs' : q ∣ aliquot t := dvd_trans hqs (Nat.div_dvd_of_dvd (reg_d_dvd_aliquot hR))
  have hqsig : q ∣ sig t := by
    rw [sig_eq_aliquot_add]; exact Nat.dvd_add hqs' hqt
  have hqd : q ∣ d := by rw [hR.1]; exact Nat.dvd_gcd hqt hqsig
  have := reg_prime_le hR ht hq hqd
  linarith

end reg

/-! ## Coprimality facts for the collision pair -/

theorem prime_not_dvd_both {a b q : ℕ} (hab : Nat.Coprime a b) (hq : q.Prime) (ha : q ∣ a)
    (hb : q ∣ b) : False := by
  have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left ha hab) hb
  exact hq.one_lt.ne' this

/-- The core of `Claim_SvLargeHUnits`: with `n = qℓ`, `q ∤ ℓ`, regularity at `n` and `ℓ` with the
same `d`, and `h ∣ s(n)/d`, `h` is coprime to `s(ℓ)σ(ℓ)`. -/
theorem units_core {Y : ℝ} {d q l h n : ℕ} (hn : n = q * l) (hq : q.Prime) (hl : l ≠ 0)
    (hql : ¬ q ∣ l) (hRn : SV.RegularAt Y d n) (hRl : SV.RegularAt Y d l)
    (hh : h ∣ aliquot n / d) : Nat.Coprime h (aliquot l * sig l) := by
  subst hn
  have hn0 : q * l ≠ 0 := Nat.mul_ne_zero hq.ne_zero hl
  have hcop := reg_coprime hRn hn0
  have hS : aliquot (q * l) = q * aliquot l + sig l := aliquot_prime_mul q l hq hql
  have hhS : h ∣ aliquot (q * l) := dvd_trans hh (Nat.div_dvd_of_dvd (reg_d_dvd_aliquot hRn))
  -- a prime dividing `h` and `σ(ℓ)` is impossible
  have key : ∀ q₀ : ℕ, q₀.Prime → q₀ ∣ h → q₀ ∣ sig l → False := by
    intro q₀ hq₀ h1 h2
    have hq₀S : q₀ ∣ aliquot (q * l) := dvd_trans h1 hhS
    have hq₀qs : q₀ ∣ q * aliquot l := by
      rw [hS] at hq₀S; exact (Nat.dvd_add_left h2).mp hq₀S
    have hq₀d : q₀ ∣ d := by
      rcases (Nat.Prime.dvd_mul hq₀).mp hq₀qs with h3 | h3
      · -- q₀ = q
        have hq₀n : q₀ ∣ q * l := dvd_mul_of_dvd_left h3 l
        have hq₀sig : q₀ ∣ sig (q * l) := by
          rw [sig_eq_aliquot_add]; exact Nat.dvd_add hq₀S hq₀n
        rw [hRn.1]; exact Nat.dvd_gcd hq₀n hq₀sig
      · have hq₀l : q₀ ∣ l := by
          rw [sig_eq_aliquot_add] at h2; exact (Nat.dvd_add_right h3).mp h2
        rw [hRl.1]; exact Nat.dvd_gcd hq₀l h2
    exact prime_not_dvd_both hcop hq₀ hq₀d (dvd_trans h1 hh)
  apply Nat.Coprime.mul_right
  · apply Nat.coprime_of_dvd
    intro q₀ hq₀ h1 h2
    have hq₀S : q₀ ∣ aliquot (q * l) := dvd_trans h1 hhS
    have : q₀ ∣ sig l := by
      rw [hS] at hq₀S; exact (Nat.dvd_add_right (dvd_mul_of_dvd_right h2 q)).mp hq₀S
    exact key q₀ hq₀ h1 this
  · apply Nat.coprime_of_dvd
    intro q₀ hq₀ h1 h2
    exact key q₀ hq₀ h1 h2

/-! ## The large-`h` congruence and rigidity: pure arithmetic -/

/-- Elimination of `q, q'` (`eq:sv-large-h-congruence`): from the collision
`s(p·qℓ) = s(p'·q'ℓ')` and `h ∣ s(qℓ), h ∣ s(q'ℓ')`. -/
theorem congr_core {p p' q q' l l' h n n' : ℕ} (hn : n = q * l) (hn' : n' = q' * l')
    (hp : p.Prime) (hp' : p'.Prime) (hq : q.Prime)
    (hq' : q'.Prime) (hpn : ¬ p ∣ n) (hpn' : ¬ p' ∣ n') (hql : ¬ q ∣ l)
    (hql' : ¬ q' ∣ l') (hS : h ∣ aliquot n) (hS' : h ∣ aliquot n')
    (hcol : aliquot (p * n) = aliquot (p' * n')) :
    (h : ℤ) ∣ (aliquot l' : ℤ) * (l : ℤ) * (sig l : ℤ) -
      (aliquot l : ℤ) * (l' : ℤ) * (sig l' : ℤ) := by
  subst hn hn'
  have e1n := aliquot_prime_mul p (q * l) hp hpn
  have e1n' := aliquot_prime_mul p' (q' * l') hp' hpn'
  have E1 : (p : ℤ) * (aliquot (q * l) : ℤ) + (sig (q * l) : ℤ) =
      (p' : ℤ) * (aliquot (q' * l') : ℤ) + (sig (q' * l') : ℤ) := by
    have := e1n.symm.trans (hcol.trans e1n')
    exact_mod_cast this
  have E2 : (sig (q * l) : ℤ) = (aliquot (q * l) : ℤ) + (q : ℤ) * (l : ℤ) := by
    have := sig_eq_aliquot_add (q * l)
    exact_mod_cast this
  have E3 : (sig (q' * l') : ℤ) = (aliquot (q' * l') : ℤ) + (q' : ℤ) * (l' : ℤ) := by
    have := sig_eq_aliquot_add (q' * l')
    exact_mod_cast this
  have E6 : (aliquot (q * l) : ℤ) = (q : ℤ) * (aliquot l : ℤ) + (sig l : ℤ) := by
    have := aliquot_prime_mul q l hq hql
    exact_mod_cast this
  have E7 : (aliquot (q' * l') : ℤ) = (q' : ℤ) * (aliquot l' : ℤ) + (sig l' : ℤ) := by
    have := aliquot_prime_mul q' l' hq' hql'
    exact_mod_cast this
  have key : (aliquot l' : ℤ) * (l : ℤ) * (sig l : ℤ) - (aliquot l : ℤ) * (l' : ℤ) * (sig l' : ℤ) =
      (aliquot (q * l) : ℤ) * ((aliquot l' : ℤ) * l + (aliquot l : ℤ) * (aliquot l' : ℤ) * (p + 1)) -
      (aliquot (q' * l') : ℤ) * ((aliquot l : ℤ) * l' + (aliquot l : ℤ) * (aliquot l' : ℤ) * (p' + 1)) := by
    linear_combination (-((aliquot l' : ℤ) * l)) * E6 + ((aliquot l : ℤ) * l') * E7 -
      ((aliquot l : ℤ) * (aliquot l' : ℤ)) * (E1 - E2 + E3)
  rw [key]
  have hSZ : (h : ℤ) ∣ (aliquot (q * l) : ℤ) := by exact_mod_cast hS
  have hSZ' : (h : ℤ) ∣ (aliquot (q' * l') : ℤ) := by exact_mod_cast hS'
  exact Int.dvd_sub (Dvd.dvd.mul_right hSZ _) (Dvd.dvd.mul_right hSZ' _)

/-- The reduced-denominator argument (EP1054.tex lines 1690–1708): `ℓ²/s(ℓ) + ℓ = ℓ'²/s(ℓ') + ℓ'`
with both fractions of reduced denominator `s/d`, `s'/d` forces `s = s'` and `ℓ = ℓ'`. -/
theorem rigid_core {s s' l l' d : ℕ} (hd : d ≠ 0) (hs : s ≠ 0) (hds : d ∣ s) (hds' : d ∣ s')
    (hdl : d ∣ l ^ 2) (hdl' : d ∣ l' ^ 2) (hc : Nat.Coprime (s / d) (l ^ 2 / d))
    (hc' : Nat.Coprime (s' / d) (l' ^ 2 / d)) (hE : s' * l * (s + l) = s * l' * (s' + l')) :
    s = s' ∧ l = l' := by
  obtain ⟨a, rfl⟩ := hds
  obtain ⟨a', rfl⟩ := hds'
  obtain ⟨b, hb⟩ := hdl
  obtain ⟨b', hb'⟩ := hdl'
  have hd0 : 0 < d := Nat.pos_of_ne_zero hd
  rw [Nat.mul_div_cancel_left a hd0, hb, Nat.mul_div_cancel_left b hd0] at hc
  rw [Nat.mul_div_cancel_left a' hd0, hb', Nat.mul_div_cancel_left b' hd0] at hc'
  have hEZ : ((d : ℤ) * a') * l * ((d : ℤ) * a + l) = ((d : ℤ) * a) * l' * ((d : ℤ) * a' + l') := by
    exact_mod_cast hE
  have hbZ : (l : ℤ) ^ 2 = (d : ℤ) * b := by exact_mod_cast hb
  have hbZ' : (l' : ℤ) ^ 2 = (d : ℤ) * b' := by exact_mod_cast hb'
  have h1 : ((d : ℤ) * d) * (a * a' * l + a' * b) = ((d : ℤ) * d) * (a * a' * l' + a * b') := by
    linear_combination hEZ - ((d : ℤ) * a') * hbZ + ((d : ℤ) * a) * hbZ'
  have hdd : ((d : ℤ) * d) ≠ 0 := by positivity
  have key : (a : ℤ) * a' * l + a' * b = a * a' * l' + a * b' := mul_left_cancel₀ hdd h1
  have hab : a ∣ a' * b := by
    have : (a : ℤ) ∣ (a' : ℤ) * b := ⟨a' * l' + b' - a' * l, by linear_combination key⟩
    exact_mod_cast this
  have hab' : a' ∣ a * b' := by
    have : (a' : ℤ) ∣ (a : ℤ) * b' := ⟨a * l - a * l' + b, by linear_combination -key⟩
    exact_mod_cast this
  have h2 : a ∣ a' := hc.dvd_of_dvd_mul_right hab
  have h3 : a' ∣ a := hc'.dvd_of_dvd_mul_right hab'
  have haa : a = a' := Nat.dvd_antisymm h2 h3
  subst haa
  refine ⟨rfl, ?_⟩
  have hs0 : 0 < d * a := Nat.pos_of_ne_zero hs
  have h4 : l * (d * a + l) = l' * (d * a + l') := by
    have : (d * a) * (l * (d * a + l)) = (d * a) * (l' * (d * a + l')) := by
      calc (d * a) * (l * (d * a + l)) = d * a * l * (d * a + l) := by ring
        _ = d * a * l' * (d * a + l') := hE
        _ = (d * a) * (l' * (d * a + l')) := by ring
    exact Nat.eq_of_mul_eq_mul_left hs0 this
  rcases lt_trichotomy l l' with h5 | h5 | h5
  · exfalso
    have : l * (d * a + l) < l' * (d * a + l') :=
      Nat.mul_lt_mul_of_lt_of_le h5 (by omega) (by omega)
    omega
  · exact h5
  · exfalso
    have : l' * (d * a + l') < l * (d * a + l) :=
      Nat.mul_lt_mul_of_lt_of_le h5 (by omega) (by omega)
    omega

theorem prod3_le {a b c u v w : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hau : a ≤ u)
    (hbv : b ≤ v) (hcw : c ≤ w) : a * b * c ≤ u * v * w := by
  have hu : 0 ≤ u := le_trans ha hau
  have hv : 0 ≤ v := le_trans hb hbv
  exact mul_le_mul (mul_le_mul hau hbv hb hu) hcw hc (mul_nonneg hu hv)

/-- From `Eq_SvTwoSided`: `s(t) < C t` and `σ(t) ≤ (C+1) t` for `t > 0`. -/
theorem aliquot_lt_of_ratio {t : ℕ} {C : ℝ} (ht : 0 < t) (h : (aliquot t : ℝ) / t < C) :
    (aliquot t : ℝ) < C * t := by
  have : (0 : ℝ) < t := by exact_mod_cast ht
  rwa [div_lt_iff₀ this] at h

theorem aliquot_gt_of_ratio {t : ℕ} {c : ℝ} (ht : 0 < t) (h : c < (aliquot t : ℝ) / t) :
    c * t < (aliquot t : ℝ) := by
  have : (0 : ℝ) < t := by exact_mod_cast ht
  rwa [lt_div_iff₀ this] at h

/-! ## Links: the large-`h` claims -/

theorem gcdS_div_dvd_left {d n n' : ℕ} (hd : d ∣ SV.gcdS n n') :
    SV.gcdS n n' / d ∣ aliquot n / d :=
  Nat.div_dvd_div hd (Nat.gcd_dvd_left _ _)

theorem gcdS_div_dvd_right {d n n' : ℕ} (hd : d ∣ SV.gcdS n n') :
    SV.gcdS n n' / d ∣ aliquot n' / d :=
  Nat.div_dvd_div hd (Nat.gcd_dvd_right _ _)

theorem link_units : Spine.Link_Claim_SvLargeHUnits := by
  intro _hcol δ _hδ _hδ1 D _hD 𝒜 hreg
  obtain ⟨c, _hc, B, _hB, X₀, hX₀⟩ := hreg
  refine ⟨max X₀ 1, fun X hX d p q r k p' q' r' k' ht ht' _hne _hcoll _hh => ?_⟩
  have hXX₀ : X₀ ≤ X := le_trans (le_max_left _ _) hX
  have hX1 : 1 ≤ X := le_trans (le_max_right _ _) hX
  have hA := (hX₀ X hXX₀).2.2
  obtain ⟨-, hRl, hRn, -, -, -, -⟩ := member_reg hA ht
  obtain ⟨-, hRl', hRn', -, -, -, -⟩ := member_reg hA ht'
  have hT := ht.1
  have hT' := ht'.1
  have hn0 := (tuple_n_pos hX1 hT).ne'
  have hn0' := (tuple_n_pos hX1 hT').ne'
  have hd : d ∣ SV.gcdS (q * r * k) (q' * r' * k') :=
    Nat.dvd_gcd (reg_d_dvd_aliquot hRn) (reg_d_dvd_aliquot hRn')
  have hl0 : r * k ≠ 0 := Nat.mul_ne_zero hT.2.2.1.ne_zero (tuple_k_pos (by linarith) hT).ne'
  have hl0' : r' * k' ≠ 0 := Nat.mul_ne_zero hT'.2.2.1.ne_zero (tuple_k_pos (by linarith) hT').ne'
  exact ⟨units_core (mul_assoc q r k) hT.2.1 hl0 (tuple_q_not_dvd hX1 hT) hRn hRl
      (gcdS_div_dvd_left hd),
    units_core (mul_assoc q' r' k') hT'.2.1 hl0' (tuple_q_not_dvd hX1 hT') hRn' hRl'
      (gcdS_div_dvd_right hd)⟩

theorem link_congruence : Spine.Link_Eq_SvLargeHCongruence := by
  intro _hcol δ _hδ _hδ1 D _hD 𝒜 hreg
  obtain ⟨c, _hc, B, _hB, X₀, hX₀⟩ := hreg
  refine ⟨max X₀ (2 ^ 15), fun X hX d p q r k p' q' r' k' ht ht' _hne hcoll _hh => ?_⟩
  have hXX₀ : X₀ ≤ X := le_trans (le_max_left _ _) hX
  have hX15 : 2 ^ 15 ≤ X := le_trans (le_max_right _ _) hX
  have hX1 : 1 ≤ X := by linarith
  have hA := (hX₀ X hXX₀).2.2
  obtain ⟨-, -, hRn, -, -, -, -⟩ := member_reg hA ht
  obtain ⟨-, -, hRn', -, -, -, -⟩ := member_reg hA ht'
  have hT := ht.1
  have hT' := ht'.1
  have hd : d ∣ SV.gcdS (q * r * k) (q' * r' * k') :=
    Nat.dvd_gcd (reg_d_dvd_aliquot hRn) (reg_d_dvd_aliquot hRn')
  have hS : SV.gcdS (q * r * k) (q' * r' * k') / d ∣ aliquot (q * r * k) :=
    (Nat.div_dvd_of_dvd hd).trans (Nat.gcd_dvd_left _ _)
  have hS' : SV.gcdS (q * r * k) (q' * r' * k') / d ∣ aliquot (q' * r' * k') :=
    (Nat.div_dvd_of_dvd hd).trans (Nat.gcd_dvd_right _ _)
  have hpn := tuple_p_not_dvd hX15 hT
  have hpn' := tuple_p_not_dvd hX15 hT'
  have hcoll' : aliquot (p * (q * r * k)) = aliquot (p' * (q' * r' * k')) := by
    have e1 : p * (q * r * k) = p * q * r * k := by ring
    have e2 : p' * (q' * r' * k') = p' * q' * r' * k' := by ring
    rw [e1, e2]; exact hcoll
  exact congr_core (mul_assoc q r k) (mul_assoc q' r' k') hT.1 hT'.1 hT.2.1 hT'.2.1 hpn hpn'
    (tuple_q_not_dvd hX1 hT) (tuple_q_not_dvd hX1 hT') hS hS' hcoll'

theorem link_sigmaDistinct : Spine.Link_Claim_SvSigmaDistinct := by
  intro hTS _hcol δ hδ hδ1 D hD 𝒜 _hreg
  obtain ⟨Cδ, hCδ, X₃, hX₃⟩ := hTS δ hδ hδ1 D hD
  refine ⟨max X₃ (max (2 ^ 15) ((2 * Cδ) ^ 15)), ?_⟩
  intro X hX d n n' hpair hsig
  obtain ⟨hne, p, p', ⟨q, r, k, ht, rfl⟩, ⟨q', r', k', ht', rfl⟩, hcoll⟩ := hpair
  have hX3 : X₃ ≤ X := le_trans (le_max_left _ _) hX
  have hX15 : 2 ^ 15 ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hX
  have hXC : (2 * Cδ) ^ 15 ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hX
  have hX1 : 1 ≤ X := by linarith
  have hT := ht.1
  have hT' := ht'.1
  have h2C : 2 * Cδ ≤ X ^ ((1 : ℝ) / 15) := by
    have := le_rpow_inv (n := 15) (by norm_num) (by linarith : (0 : ℝ) ≤ 2 * Cδ) hXC
    simpa using this
  -- the collision identity at both members
  have e := aliquot_prime_mul p _ hT.1 (tuple_p_not_dvd hX15 hT)
  have e' := aliquot_prime_mul p' _ hT'.1 (tuple_p_not_dvd hX15 hT')
  have hcoll' : p * aliquot (q * r * k) = p' * aliquot (q' * r' * k') := by
    have := e.symm.trans (hcoll.trans e')
    rw [hsig] at this
    omega
  -- the bound `s(n') < p`
  have hn'pos := tuple_n_pos hX1 hT'
  have hrat := hX₃ X hX3 p' q' r' k' hT' (q' * r' * k') (Or.inr (Or.inr (Or.inl rfl)))
  have hs'lt : (aliquot (q' * r' * k') : ℝ) < Cδ * ((q' * r' * k' : ℕ) : ℝ) :=
    aliquot_lt_of_ratio hn'pos hrat.2
  have hs'pos : 0 < aliquot (q' * r' * k') := by
    have h1 := aliquot_gt_of_ratio hn'pos hrat.1
    have : (0 : ℝ) < (aliquot (q' * r' * k') : ℝ) := by
      have : (0 : ℝ) < 1 / δ * ((q' * r' * k' : ℕ) : ℝ) := by
        have : (0 : ℝ) < ((q' * r' * k' : ℕ) : ℝ) := by exact_mod_cast hn'pos
        positivity
      linarith
    exact_mod_cast this
  have hpbig : Cδ * ((q' * r' * k' : ℕ) : ℝ) < p :=
    tuple_p_gt_mul hX1 hT hCδ.le (tuple_n_le hX1 hT') h2C
  have hs'p : aliquot (q' * r' * k') < p := by
    have : (aliquot (q' * r' * k') : ℝ) < p := by linarith
    exact_mod_cast this
  have hpp : p = p' := by
    by_contra hpp
    have hcop : Nat.Coprime p p' := (Nat.coprime_primes hT.1 hT'.1).2 hpp
    have : p ∣ p' * aliquot (q' * r' * k') := ⟨aliquot (q * r * k), hcoll'.symm⟩
    have := Nat.le_of_dvd hs'pos (hcop.dvd_of_dvd_mul_left this)
    omega
  subst hpp
  have hss : aliquot (q * r * k) = aliquot (q' * r' * k') :=
    Nat.eq_of_mul_eq_mul_left hT.1.pos hcoll'
  apply hne
  have h1 := sig_eq_aliquot_add (q * r * k)
  have h2 := sig_eq_aliquot_add (q' * r' * k')
  omega

theorem link_rigidity : Spine.Link_Claim_SvLargeHRigidity := by
  intro hcong hTS hunits _hColl δ hδ hδ1 D hD 𝒜 hreg
  obtain ⟨X₁, hX₁⟩ := hcong δ hδ hδ1 D hD 𝒜 hreg
  obtain ⟨X₂, hX₂⟩ := hunits δ hδ hδ1 D hD 𝒜 hreg
  obtain ⟨Cδ, hCδ, X₃, hX₃⟩ := hTS δ hδ hδ1 D hD
  obtain ⟨c, _hc, B, _hB, X₀, hX₀⟩ := hreg
  have hK0 : 0 ≤ Cδ * (Cδ + 1) := by positivity
  refine ⟨max (max X₀ X₁) (max (max X₂ X₃) (max ((Cδ * (Cδ + 1)) ^ 330) 1)), ?_⟩
  intro X hX d p q r k p' q' r' k' ht ht' hne hcoll hh
  have hXa : X₀ ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hXb : X₁ ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hXc : X₂ ≤ X :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_right _ _))) hX
  have hXd : X₃ ≤ X :=
    le_trans (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_right _ _))) hX
  have hXe : (Cδ * (Cδ + 1)) ^ 330 ≤ X :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hX
  have hX1 : 1 ≤ X :=
    le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hX
  have hX0 : 0 < X := by linarith
  have hA := (hX₀ X hXa).2.2
  obtain ⟨-, hRl, hRn, -, -, -, -⟩ := member_reg hA ht
  obtain ⟨-, hRl', hRn', -, -, -, -⟩ := member_reg hA ht'
  have hT := ht.1
  have hT' := ht'.1
  have hcong' := hX₁ X hXb d p q r k p' q' r' k' ht ht' hne hcoll hh
  have hun := hX₂ X hXc d p q r k p' q' r' k' ht ht' hne hcoll hh
  have hl0 : 0 < r * k := Nat.mul_pos hT.2.2.1.pos (tuple_k_pos hX0.le hT)
  have hl0' : 0 < r' * k' := Nat.mul_pos hT'.2.2.1.pos (tuple_k_pos hX0.le hT')
  have hrat := hX₃ X hXd p q r k hT (r * k) (Or.inr (Or.inl rfl))
  have hrat' := hX₃ X hXd p' q' r' k' hT' (r' * k') (Or.inr (Or.inl rfl))
  have hsl : (aliquot (r * k) : ℝ) < Cδ * ((r * k : ℕ) : ℝ) := aliquot_lt_of_ratio hl0 hrat.2
  have hsl' : (aliquot (r' * k') : ℝ) < Cδ * ((r' * k' : ℕ) : ℝ) :=
    aliquot_lt_of_ratio hl0' hrat'.2
  have hll := tuple_l_le hX1 hT
  have hll' := tuple_l_le hX1 hT'
  have hsig : (sig (r * k) : ℝ) ≤ (Cδ + 1) * ((r * k : ℕ) : ℝ) := by
    have := sig_eq_aliquot_add (r * k)
    have h2 : (sig (r * k) : ℝ) = (aliquot (r * k) : ℝ) + ((r * k : ℕ) : ℝ) := by exact_mod_cast this
    rw [h2]; linarith
  have hsig' : (sig (r' * k') : ℝ) ≤ (Cδ + 1) * ((r' * k' : ℕ) : ℝ) := by
    have := sig_eq_aliquot_add (r' * k')
    have h2 : (sig (r' * k') : ℝ) = (aliquot (r' * k') : ℝ) + ((r' * k' : ℕ) : ℝ) := by
      exact_mod_cast this
    rw [h2]; linarith
  have hX3 : X ^ ((1 : ℝ) / 10) * X ^ ((1 : ℝ) / 10) * X ^ ((1 : ℝ) / 10) = X ^ ((3 : ℝ) / 10) := by
    rw [rpow_mul_rpow hX0, rpow_mul_rpow hX0]; norm_num
  have hKX : Cδ * (Cδ + 1) * X ^ ((3 : ℝ) / 10) ≤ X ^ ((10 : ℝ) / 33) := by
    have h1 : Cδ * (Cδ + 1) ≤ X ^ ((1 : ℝ) / 330) := by
      have := le_rpow_inv (n := 330) (by norm_num) hK0 hXe
      simpa using this
    have h2 : X ^ ((10 : ℝ) / 33) = X ^ ((1 : ℝ) / 330) * X ^ ((3 : ℝ) / 10) := by
      rw [rpow_mul_rpow hX0]; norm_num
    rw [h2]
    exact mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hX0.le _)
  have hlnn : (0 : ℝ) ≤ ((r * k : ℕ) : ℝ) := Nat.cast_nonneg _
  have hlnn' : (0 : ℝ) ≤ ((r' * k' : ℕ) : ℝ) := Nat.cast_nonneg _
  have hAle : (aliquot (r' * k') : ℝ) * ((r * k : ℕ) : ℝ) * (sig (r * k) : ℝ) <
      ((SV.gcdS (q * r * k) (q' * r' * k') / d : ℕ) : ℝ) := by
    calc (aliquot (r' * k') : ℝ) * ((r * k : ℕ) : ℝ) * (sig (r * k) : ℝ)
        ≤ (Cδ * ((r' * k' : ℕ) : ℝ)) * ((r * k : ℕ) : ℝ) * ((Cδ + 1) * ((r * k : ℕ) : ℝ)) :=
          prod3_le (Nat.cast_nonneg _) hlnn (Nat.cast_nonneg _) hsl'.le le_rfl hsig
      _ = Cδ * (Cδ + 1) * (((r' * k' : ℕ) : ℝ) * ((r * k : ℕ) : ℝ) * ((r * k : ℕ) : ℝ)) := by ring
      _ ≤ Cδ * (Cδ + 1) * (X ^ ((1 : ℝ) / 10) * X ^ ((1 : ℝ) / 10) * X ^ ((1 : ℝ) / 10)) :=
          mul_le_mul_of_nonneg_left (prod3_le hlnn' hlnn hlnn hll' hll hll) hK0
      _ = Cδ * (Cδ + 1) * X ^ ((3 : ℝ) / 10) := by rw [hX3]
      _ ≤ X ^ ((10 : ℝ) / 33) := hKX
      _ < _ := hh
  have hBle : (aliquot (r * k) : ℝ) * ((r' * k' : ℕ) : ℝ) * (sig (r' * k') : ℝ) <
      ((SV.gcdS (q * r * k) (q' * r' * k') / d : ℕ) : ℝ) := by
    calc (aliquot (r * k) : ℝ) * ((r' * k' : ℕ) : ℝ) * (sig (r' * k') : ℝ)
        ≤ (Cδ * ((r * k : ℕ) : ℝ)) * ((r' * k' : ℕ) : ℝ) * ((Cδ + 1) * ((r' * k' : ℕ) : ℝ)) :=
          prod3_le (Nat.cast_nonneg _) hlnn' (Nat.cast_nonneg _) hsl.le le_rfl hsig'
      _ = Cδ * (Cδ + 1) * (((r * k : ℕ) : ℝ) * ((r' * k' : ℕ) : ℝ) * ((r' * k' : ℕ) : ℝ)) := by ring
      _ ≤ Cδ * (Cδ + 1) * (X ^ ((1 : ℝ) / 10) * X ^ ((1 : ℝ) / 10) * X ^ ((1 : ℝ) / 10)) :=
          mul_le_mul_of_nonneg_left (prod3_le hlnn hlnn' hlnn' hll hll' hll') hK0
      _ = Cδ * (Cδ + 1) * X ^ ((3 : ℝ) / 10) := by rw [hX3]
      _ ≤ X ^ ((10 : ℝ) / 33) := hKX
      _ < _ := hh
  have hAZ : (aliquot (r' * k') : ℤ) * ((r * k : ℕ) : ℤ) * (sig (r * k) : ℤ) <
      ((SV.gcdS (q * r * k) (q' * r' * k') / d : ℕ) : ℤ) := by exact_mod_cast hAle
  have hBZ : (aliquot (r * k) : ℤ) * ((r' * k' : ℕ) : ℤ) * (sig (r' * k') : ℤ) <
      ((SV.gcdS (q * r * k) (q' * r' * k') / d : ℕ) : ℤ) := by exact_mod_cast hBle
  have hA0 : (0 : ℤ) ≤ (aliquot (r' * k') : ℤ) * ((r * k : ℕ) : ℤ) * (sig (r * k) : ℤ) := by
    positivity
  have hB0 : (0 : ℤ) ≤ (aliquot (r * k) : ℤ) * ((r' * k' : ℕ) : ℤ) * (sig (r' * k') : ℤ) := by
    positivity
  have hE0 := Int.eq_zero_of_abs_lt_dvd hcong' (abs_lt.mpr ⟨by linarith, by linarith⟩)
  have hEN : aliquot (r' * k') * (r * k) * sig (r * k) =
      aliquot (r * k) * (r' * k') * sig (r' * k') := by
    have := sub_eq_zero.mp hE0
    exact_mod_cast this
  rw [sig_eq_aliquot_add (r * k), sig_eq_aliquot_add (r' * k')] at hEN
  have hdl := reg_d_dvd hRl
  have hdl' := reg_d_dvd hRl'
  obtain ⟨hss, hll_eq⟩ := rigid_core (reg_d_ne hRl hl0.ne') (reg_aliquot_ne hRl hl0.ne')
    (reg_d_dvd_aliquot hRl) (reg_d_dvd_aliquot hRl') (dvd_pow hdl two_ne_zero)
    (dvd_pow hdl' two_ne_zero) (reg_coprime_sq hRl hl0.ne') (reg_coprime_sq hRl' hl0'.ne') hEN
  refine ⟨hll_eq, ?_⟩
  -- `q ≡ q' (mod h)`
  have hd : d ∣ SV.gcdS (q * r * k) (q' * r' * k') :=
    Nat.dvd_gcd (reg_d_dvd_aliquot hRn) (reg_d_dvd_aliquot hRn')
  have hS : SV.gcdS (q * r * k) (q' * r' * k') / d ∣ aliquot (q * r * k) :=
    (Nat.div_dvd_of_dvd hd).trans (Nat.gcd_dvd_left _ _)
  have hS' : SV.gcdS (q * r * k) (q' * r' * k') / d ∣ aliquot (q' * r' * k') :=
    (Nat.div_dvd_of_dvd hd).trans (Nat.gcd_dvd_right _ _)
  have e1 : aliquot (q * r * k) = q * aliquot (r * k) + sig (r * k) := by
    rw [mul_assoc]; exact aliquot_prime_mul q (r * k) hT.2.1 (tuple_q_not_dvd hX1 hT)
  have e2 : aliquot (q' * r' * k') = q' * aliquot (r * k) + sig (r * k) := by
    rw [mul_assoc, ← hll_eq]
    exact aliquot_prime_mul q' (r * k) hT'.2.1 (hll_eq ▸ tuple_q_not_dvd hX1 hT')
  rw [e1] at hS
  rw [e2] at hS'
  have hm1 := (Nat.modEq_zero_iff_dvd.mpr hS).trans (Nat.modEq_zero_iff_dvd.mpr hS').symm
  have hm2 := Nat.ModEq.add_right_cancel' (sig (r * k)) hm1
  have hcop : Nat.Coprime (SV.gcdS (q * r * k) (q' * r' * k') / d) (aliquot (r * k)) :=
    Nat.Coprime.coprime_dvd_right (dvd_mul_right _ _) hun.1
  exact Nat.ModEq.cancel_right_of_coprime hcop hm2

/-! ## `m/φ(m)` as an Euler product -/

theorem phiRatio_eq_prod {m : ℕ} (hm : m ≠ 0) :
    SV.phiRatio m = ∏ p ∈ m.primeFactors, (p : ℝ) / ((p : ℝ) - 1) := by
  have h := Nat.totient_mul_prod_primeFactors m
  have hR : (m.totient : ℝ) * ∏ p ∈ m.primeFactors, (p : ℝ) =
      (m : ℝ) * ∏ p ∈ m.primeFactors, ((p : ℝ) - 1) := by
    have h' : ((m.totient * ∏ p ∈ m.primeFactors, p : ℕ) : ℝ) =
        ((m * ∏ p ∈ m.primeFactors, (p - 1) : ℕ) : ℝ) := by rw [h]
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_prod, Nat.cast_prod] at h'
    rw [h']
    congr 1
    refine Finset.prod_congr rfl (fun p hp => ?_)
    rw [Nat.cast_sub (Nat.pos_of_mem_primeFactors hp), Nat.cast_one]
  have ht : (m.totient : ℝ) ≠ 0 := by
    have : 0 < m.totient := Nat.totient_pos.2 (Nat.pos_of_ne_zero hm)
    exact_mod_cast this.ne'
  have hpp : (∏ p ∈ m.primeFactors, ((p : ℝ) - 1)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro p hp
    have : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    linarith
  unfold SV.phiRatio
  rw [Finset.prod_div_distrib, div_eq_div_iff ht hpp]
  linarith [hR]

theorem prod_ratio_nonneg (s : Finset ℕ) (hs : ∀ p ∈ s, 1 ≤ p) :
    0 ≤ ∏ p ∈ s, (p : ℝ) / ((p : ℝ) - 1) := by
  apply Finset.prod_nonneg
  intro p hp
  have : (1 : ℝ) ≤ p := by exact_mod_cast hs p hp
  apply div_nonneg <;> linarith

/-- `∏_{p ∈ s} p/(p−1) = v/φ(v)` for a finite set `s` of primes and `v = ∏_{p∈s} p`. -/
theorem prod_ratio_eq_phiRatio (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    ∏ p ∈ s, (p : ℝ) / ((p : ℝ) - 1) = SV.phiRatio (∏ p ∈ s, p) := by
  have hne : (∏ p ∈ s, p) ≠ 0 := Finset.prod_ne_zero_iff.2 fun p hp => (hs p hp).ne_zero
  rw [phiRatio_eq_prod hne, Nat.primeFactors_prod hs]

theorem link_A322 : Spine.Link_Claim_SvA322Reduction := by
  intro htot δ _hδ _hδ1 D _hD 𝒜 hreg
  obtain ⟨c, _hc, B, _hB, X₀, hX₀⟩ := hreg
  refine ⟨Real.pi ^ 2 / 6 * B, max X₀ 1, ?_⟩
  intro X hX d n n' hpair _hh
  have hXa : X₀ ≤ X := le_trans (le_max_left _ _) hX
  have hX1 : 1 ≤ X := le_trans (le_max_right _ _) hX
  have hA := (hX₀ X hXa).2.2
  obtain ⟨_hne, p, p', -, ⟨q', r', k', ht', rfl⟩, -⟩ := hpair
  obtain ⟨-, -, hRn', -, -, -, habund⟩ := member_reg hA ht'
  have hn'0 := (tuple_n_pos hX1 ht'.1).ne'
  have hs0 := reg_aliquot_ne hRn' hn'0
  classical
  -- split off the primes dividing `s(n')`
  set F := (SV.A3 n (q' * r' * k')).primeFactors.filter
      (fun p : ℕ => (logIt 2 X) ^ 2 < (p : ℝ) ∧ (p : ℝ) ≤ Real.log X ∧ ¬ p ∣ sig n) with hF
  have h32 : SV.ratio32 X n (q' * r' * k') = ∏ p ∈ F, (p : ℝ) / ((p : ℝ) - 1) := by
    unfold SV.ratio32; rw [hF]
  have h322 : SV.ratio322 X n (q' * r' * k') =
      ∏ p ∈ F.filter (fun p => ¬ p ∣ aliquot (q' * r' * k')), (p : ℝ) / ((p : ℝ) - 1) := by
    unfold SV.ratio322; rw [hF, Finset.filter_filter]
    refine Finset.prod_congr ?_ (fun _ _ => rfl)
    ext p
    simp only [Finset.mem_filter, and_assoc]
  rw [h32, h322, ← Finset.prod_filter_mul_prod_filter_not F (fun p => p ∣ aliquot (q' * r' * k'))]
  have hFp : ∀ p ∈ F, p.Prime := fun p hp =>
    Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hp).1
  set G := F.filter (fun p => p ∣ aliquot (q' * r' * k')) with hG
  have hGp : ∀ p ∈ G, p.Prime := fun p hp => hFp p (Finset.mem_filter.1 hp).1
  have hGd : ∀ p ∈ G, p ∣ aliquot (q' * r' * k') := fun p hp => (Finset.mem_filter.1 hp).2
  have hv : (∏ p ∈ G, p) ∣ aliquot (q' * r' * k') :=
    Finset.prod_primes_dvd _ (fun p hp => (hGp p hp).prime) hGd
  have hv0 : 1 ≤ ∏ p ∈ G, p :=
    Nat.one_le_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun p hp => (hGp p hp).ne_zero)
  obtain ⟨ht1, ht2⟩ := htot (∏ p ∈ G, p) (aliquot (q' * r' * k')) hv0
    (Nat.one_le_iff_ne_zero.2 hs0) hv
  have hGbound : ∏ p ∈ G, (p : ℝ) / ((p : ℝ) - 1) ≤ Real.pi ^ 2 / 6 * B := by
    rw [prod_ratio_eq_phiRatio G hGp]
    unfold SV.phiRatio
    calc _ ≤ Real.pi ^ 2 / 6 * abundancy (∏ p ∈ G, p) := ht1
      _ ≤ Real.pi ^ 2 / 6 * abundancy (aliquot (q' * r' * k')) :=
          mul_le_mul_of_nonneg_left ht2 (by positivity)
      _ ≤ Real.pi ^ 2 / 6 * B := mul_le_mul_of_nonneg_left habund (by positivity)
  have hrest : 0 ≤ ∏ p ∈ F.filter (fun p => ¬ p ∣ aliquot (q' * r' * k')),
      (p : ℝ) / ((p : ℝ) - 1) :=
    prod_ratio_nonneg _ (fun p hp => (hFp p (Finset.mem_filter.1 hp).1).one_lt.le)
  exact mul_le_mul_of_nonneg_right hGbound hrest

/-! ## Assembling the reduced collision sum -/

theorem reducedSum_split (D : ℕ) (A : Finset ℕ) (X : ℝ) (d : ℕ) :
    SV.reducedCollisionSum D A X d (fun _ => True) =
      SV.reducedCollisionSum D A X d (fun h => X ^ ((10 : ℝ) / 33) < (h : ℝ)) +
        SV.reducedCollisionSum D A X d (fun h => (h : ℝ) ≤ X ^ ((10 : ℝ) / 33)) := by
  classical
  unfold SV.reducedCollisionSum
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun nn _ => ?_)
  by_cases hc : SV.CollisionPair D A X d nn.1 nn.2
  · by_cases hb : X ^ ((10 : ℝ) / 33) < ((SV.gcdS nn.1 nn.2 / d : ℕ) : ℝ)
    · have hb' : ¬ ((SV.gcdS nn.1 nn.2 / d : ℕ) : ℝ) ≤ X ^ ((10 : ℝ) / 33) := not_le.mpr hb
      simp [hc, hb, hb']
    · have hb' : ((SV.gcdS nn.1 nn.2 / d : ℕ) : ℝ) ≤ X ^ ((10 : ℝ) / 33) := not_lt.mp hb
      simp [hc, hb, hb']
  · simp [hc]

theorem link_reducedSum : Spine.Link_Eq_SvReducedCollisionSum := by
  intro hlarge hsmall δ hδ hδ1 D hD 𝒜 hreg c c₁ c₂ c₃ hc hc₁ hc₂ hc₃
  obtain ⟨X₁, hX₁⟩ := hlarge δ hδ hδ1 D hD 𝒜 hreg c hc 1 one_pos
  obtain ⟨C, X₂, hX₂⟩ := hsmall δ hδ hδ1 D hD 𝒜 hreg c c₁ c₂ c₃ hc hc₁ hc₂ hc₃
  refine ⟨1 + C, max X₁ X₂, ?_⟩
  intro X hX 𝒟 hcl d hd
  have hXa : X₁ ≤ X := le_trans (le_max_left _ _) hX
  have hXb : X₂ ≤ X := le_trans (le_max_right _ _) hX
  obtain ⟨hd1, hdsm, hdY⟩ := hcl.1 d hd
  have h1 := hX₁ X hXa d hd1 hdsm hdY
  have h2 := hX₂ X hXb 𝒟 hcl d hd
  rw [reducedSum_split, mul_add, add_mul]
  linarith

/-! ## Helpers for the large-`h` sum -/

theorem prod_Ioc_ratio (M : ℕ) (hM : 1 ≤ M) :
    ∏ m ∈ Finset.Ioc 1 M, (m : ℝ) / ((m : ℝ) - 1) = M := by
  induction M, hM using Nat.le_induction with
  | base => simp
  | succ M hM ih =>
    rw [Finset.prod_Ioc_succ_top hM, ih]
    have hM0 : (M : ℝ) ≠ 0 := by
      have : (1 : ℝ) ≤ M := by exact_mod_cast hM
      linarith
    push_cast
    rw [add_sub_cancel_right]
    field_simp

/-- `A'_{3,2}/φ(A'_{3,2}) ≤ log X`: the primes involved are at most `log X`, and
`∏_{2 ≤ m ≤ M} m/(m−1) = M`. -/
theorem ratio32_le_log (X : ℝ) (hX : 1 ≤ Real.log X) (n n' : ℕ) :
    SV.ratio32 X n n' ≤ Real.log X := by
  classical
  unfold SV.ratio32
  have hM : 1 ≤ ⌊Real.log X⌋₊ := Nat.le_floor (by simpa using hX)
  calc _ ≤ ∏ m ∈ Finset.Ioc 1 ⌊Real.log X⌋₊, (m : ℝ) / ((m : ℝ) - 1) := by
        apply Finset.prod_le_prod_of_subset_of_one_le
        · intro p hp
          rw [Finset.mem_filter] at hp
          have hpp := Nat.prime_of_mem_primeFactors hp.1
          rw [Finset.mem_Ioc]
          exact ⟨hpp.one_lt, Nat.le_floor hp.2.2.1⟩
        · intro p hp
          rw [Finset.mem_filter] at hp
          have : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp.1).two_le
          apply div_nonneg <;> linarith
        · intro m hm _
          rw [Finset.mem_Ioc] at hm
          have h1 : (2 : ℝ) ≤ m := by exact_mod_cast hm.1
          rw [le_div_iff₀ (by linarith)]
          linarith
    _ = ⌊Real.log X⌋₊ := prod_Ioc_ratio _ hM
    _ ≤ Real.log X := Nat.floor_le (by linarith)

/-- Counting a residue class: `#{e ≤ N : e ≡ a (mod c), e ≠ a} · c ≤ 2N` for `a ≤ N`. -/
theorem card_residue_mul_le (N a c : ℕ) (_hc : 1 ≤ c) (ha : a ≤ N) :
    ((Finset.Icc 1 N).filter (fun e => e ≡ a [MOD c] ∧ e ≠ a)).card * c ≤ 2 * N := by
  set S := (Finset.Icc 1 N).filter (fun e => e ≡ a [MOD c] ∧ e ≠ a) with hS
  rcases S.eq_empty_or_nonempty with h0 | ⟨e₀, he₀⟩
  · rw [h0]; simp
  · -- `c ≤ N`
    rw [hS, Finset.mem_filter, Finset.mem_Icc] at he₀
    obtain ⟨⟨_, he₀N⟩, hmod, hne⟩ := he₀
    have hcN : c ≤ N := by
      rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
      · have hd : c ∣ a - e₀ := (Nat.modEq_iff_dvd' hlt.le).1 hmod
        have := Nat.le_of_dvd (by omega) hd
        omega
      · have hd : c ∣ e₀ - a := (Nat.modEq_iff_dvd' hlt.le).1 hmod.symm
        have := Nat.le_of_dvd (by omega) hd
        omega
    -- `e ↦ e / c` is injective on the class
    have hcard : S.card ≤ N / c + 1 := by
      have : S.card ≤ (Finset.range (N / c + 1)).card := by
        apply Finset.card_le_card_of_injOn (fun e => e / c)
        · intro e he
          rw [hS, Finset.coe_filter] at he
          obtain ⟨he1, -, -⟩ := he
          rw [Finset.mem_Icc] at he1
          rw [Finset.coe_range, Set.mem_Iio]
          exact Nat.lt_succ_of_le (Nat.div_le_div_right he1.2)
        · intro e he e' he' hee
          rw [hS, Finset.coe_filter] at he he'
          obtain ⟨-, h1, -⟩ := he
          obtain ⟨-, h2, -⟩ := he'
          have hm : e % c = e' % c := h1.trans h2.symm
          have := Nat.div_add_mod e c
          have := Nat.div_add_mod e' c
          simp only at hee
          rw [← Nat.div_add_mod e c, ← Nat.div_add_mod e' c, hee, hm]
      simpa using this
    calc S.card * c ≤ (N / c + 1) * c := Nat.mul_le_mul_right _ hcard
      _ = N / c * c + c := by ring
      _ ≤ N + N := Nat.add_le_add (Nat.div_mul_le_self N c) hcN
      _ = 2 * N := by ring

/-- `∑_{i ≤ n} 1/i ≤ 1 + log n`. -/
theorem sum_inv_le (n : ℕ) : ∑ i ∈ Finset.Icc 1 n, (1 : ℝ) / i ≤ 1 + Real.log n := by
  have h := harmonic_le_one_add_log n
  rw [harmonic_eq_sum_Icc] at h
  push_cast at h
  simpa [one_div] using h

theorem sum_inv_le_log {n : ℕ} {X : ℝ} (hn : (n : ℝ) ≤ X) (hX : 1 ≤ X) :
    ∑ i ∈ Finset.Icc 1 n, (1 : ℝ) / i ≤ 1 + Real.log X := by
  refine le_trans (sum_inv_le n) ?_
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · rw [h0, Nat.cast_zero, Real.log_zero]
    linarith [Real.log_nonneg hX]
  · have : (0 : ℝ) < n := by exact_mod_cast hpos
    linarith [Real.log_le_log this hn]

theorem sig_le_sq (n : ℕ) : sig n ≤ n ^ 2 := by
  show ArithmeticFunction.sigma 1 n ≤ n ^ 2
  rw [ArithmeticFunction.sigma_one_apply]
  calc ∑ d ∈ n.divisors, d ≤ ∑ _d ∈ n.divisors, n :=
        Finset.sum_le_sum (fun d hd => Nat.divisor_le hd)
    _ = n.divisors.card * n := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ n * n := Nat.mul_le_mul_right _ (Nat.card_divisors_le_self n)
    _ = n ^ 2 := by ring

theorem one_le_aliquot {m : ℕ} (hm : 2 ≤ m) : 1 ≤ aliquot m := by
  have h1 : 1 ∈ m.properDivisors := Nat.one_mem_properDivisors_iff_one_lt.2 (by omega)
  have h2 : 1 ≤ ∑ i ∈ m.properDivisors, i :=
    Finset.single_le_sum (f := fun i : ℕ => i) (fun _ _ => Nat.zero_le _) h1
  have h3 := Nat.sum_divisors_eq_sum_properDivisors_add_self (n := m)
  show 1 ≤ ArithmeticFunction.sigma 1 m - m
  rw [ArithmeticFunction.sigma_one_apply, h3]
  omega

/-! ## The level `Y` for large `X` -/

theorem logIt_two (x : ℝ) : logIt 2 x = Real.log (Real.log x) := rfl

theorem logIt_three (x : ℝ) : logIt 3 x = Real.log (Real.log (Real.log x)) := rfl

theorem log_le_div_e {t : ℝ} (ht : 0 < t) : Real.log t ≤ t / Real.exp 1 := by
  have h := Real.log_le_sub_one_of_pos (div_pos ht (Real.exp_pos 1))
  rw [Real.log_div ht.ne' (Real.exp_pos 1).ne', Real.log_exp] at h
  linarith

/-- For `X > 0`, `log X ≥ 120 e³`: `e ≤ Y ≤ log X` where `Y = Ycut X`. -/
theorem Ycut_bounds {X : ℝ} (hX0 : 0 < X) (hX : 120 * Real.exp 3 ≤ Real.log X) :
    Real.exp 1 ≤ SV.Ycut X ∧ SV.Ycut X ≤ Real.log X := by
  have he3 : 0 < Real.exp 3 := Real.exp_pos 3
  have hlu : Real.log (X ^ ((1 : ℝ) / 120)) = Real.log X / 120 := by
    rw [Real.log_rpow hX0]; ring
  set a := Real.log (Real.log (X ^ ((1 : ℝ) / 120))) with ha_def
  have ha3 : 3 ≤ a := by
    rw [ha_def, hlu]
    have : Real.exp 3 ≤ Real.log X / 120 := by linarith
    calc (3 : ℝ) = Real.log (Real.exp 3) := (Real.log_exp 3).symm
      _ ≤ Real.log (Real.log X / 120) := Real.log_le_log he3 this
  have hloga : 1 < Real.log a := by
    have h3 : Real.exp 1 < 3 := by
      have := Real.exp_one_lt_d9; linarith
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ < Real.log a := Real.log_lt_log (Real.exp_pos 1) (by linarith)
  have hY : SV.Ycut X = a / Real.log a := by
    unfold SV.Ycut SV.yOf
    rw [logIt_two, logIt_three]
  have ha0 : 0 < a := by linarith
  refine ⟨?_, ?_⟩
  · rw [hY, le_div_iff₀ (by linarith)]
    have := log_le_div_e ha0
    rw [le_div_iff₀ (Real.exp_pos 1)] at this
    linarith
  · rw [hY]
    have h1 : a / Real.log a ≤ a := div_le_self ha0.le hloga.le
    have h2 : a ≤ Real.log X / 120 := by
      rw [ha_def, hlu]
      have hp : 0 < Real.log X / 120 := by linarith
      linarith [Real.log_le_sub_one_of_pos hp]
    have h3 : Real.log X / 120 ≤ Real.log X := by
      have : 0 < Real.log X := by linarith
      linarith
    linarith

/-! ## The large-`h` sum: the bounding box of quadruples `(q', ℓ, h, q)` -/

/-- The box of quadruples `(q', ℓ, h, q)`. -/
def lhBox (NQ NL NH : ℕ) : Finset (ℕ × ℕ × ℕ × ℕ) :=
  Finset.Icc 1 NQ ×ˢ (Finset.Icc 1 NL ×ˢ (Finset.Icc 1 NH ×ˢ Finset.Icc 1 NQ))

/-- The structural conditions on `(q', ℓ, h, q)` (EP1054.tex lines 1710–1727). -/
def lhCond (X : ℝ) (y : ℕ × ℕ × ℕ × ℕ) : Prop :=
  X ^ ((3 : ℝ) / 40) < (y.2.1 : ℝ) ∧ y.2.2.1 ∣ aliquot (y.1 * y.2.1) ∧
    X ^ ((10 : ℝ) / 33) < (y.2.2.1 : ℝ) ∧ y.2.2.2 ≡ y.1 [MOD y.2.2.1] ∧ y.2.2.2 ≠ y.1 ∧
      X ^ ((7 : ℝ) / 20) < (y.2.2.2 : ℝ)

/-- The summand `d h log X/(q q' ℓ²)`. -/
noncomputable def lhG (X : ℝ) (d : ℕ) (y : ℕ × ℕ × ℕ × ℕ) : ℝ :=
  (d : ℝ) * y.2.2.1 * Real.log X / ((y.2.2.2 : ℝ) * y.1 * (y.2.1 : ℝ) ^ 2)

theorem lhG_nonneg (X : ℝ) (hL : 0 ≤ Real.log X) (d : ℕ) (y : ℕ × ℕ × ℕ × ℕ) :
    0 ≤ lhG X d y := by
  unfold lhG; positivity

/-- The `q`-sum for fixed `(q', ℓ, h)`: `∑_{q ≡ q' (h), q ≠ q'} h/q ≤ 2X^{1/60}`. -/
theorem lh_inner_q (X : ℝ) (hX0 : 0 < X) (d : ℕ) (hL : 0 ≤ Real.log X) (NQ a b c : ℕ)
    (hc : 1 ≤ c) (ha : 1 ≤ a) (haN : a ≤ NQ) (hb : 1 ≤ b)
    (hNQ : (NQ : ℝ) ≤ X ^ ((11 : ℝ) / 30)) :
    ∑ e ∈ Finset.Icc 1 NQ,
        (if e ≡ a [MOD c] ∧ e ≠ a ∧ X ^ ((7 : ℝ) / 20) < (e : ℝ) then
          lhG X d (a, b, c, e) else 0) ≤
      2 * d * Real.log X * X ^ ((1 : ℝ) / 60) / ((a : ℝ) * (b : ℝ) ^ 2) := by
  classical
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb
  have h7 : 0 < X ^ ((7 : ℝ) / 20) := Real.rpow_pos_of_pos hX0 _
  set V : ℝ := (d : ℝ) * c * Real.log X / (X ^ ((7 : ℝ) / 20) * a * (b : ℝ) ^ 2) with hV
  have hV0 : 0 ≤ V := by rw [hV]; positivity
  calc _ ≤ ∑ e ∈ Finset.Icc 1 NQ, (if e ≡ a [MOD c] ∧ e ≠ a then V else 0) := by
        apply Finset.sum_le_sum
        intro e _
        by_cases h1 : e ≡ a [MOD c] ∧ e ≠ a
        · rw [if_pos h1]
          by_cases h2 : e ≡ a [MOD c] ∧ e ≠ a ∧ X ^ ((7 : ℝ) / 20) < (e : ℝ)
          · rw [if_pos h2]
            unfold lhG
            simp only
            rw [hV]
            apply div_le_div_of_nonneg_left (by positivity) (by positivity)
            have : X ^ ((7 : ℝ) / 20) * a * (b : ℝ) ^ 2 ≤ (e : ℝ) * a * (b : ℝ) ^ 2 := by
              have := h2.2.2
              gcongr
            linarith
          · rw [if_neg h2]; exact hV0
        · rw [if_neg h1]
          by_cases h2 : e ≡ a [MOD c] ∧ e ≠ a ∧ X ^ ((7 : ℝ) / 20) < (e : ℝ)
          · exact absurd ⟨h2.1, h2.2.1⟩ h1
          · rw [if_neg h2]
    _ = ((Finset.Icc 1 NQ).filter (fun e => e ≡ a [MOD c] ∧ e ≠ a)).card * V := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    _ = (((Finset.Icc 1 NQ).filter (fun e => e ≡ a [MOD c] ∧ e ≠ a)).card * c : ℕ) *
          ((d : ℝ) * Real.log X / (X ^ ((7 : ℝ) / 20) * a * (b : ℝ) ^ 2)) := by
        rw [hV]; push_cast; ring
    _ ≤ ((2 * NQ : ℕ) : ℝ) * ((d : ℝ) * Real.log X / (X ^ ((7 : ℝ) / 20) * a * (b : ℝ) ^ 2)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast card_residue_mul_le NQ a c hc haN
    _ ≤ (2 * X ^ ((11 : ℝ) / 30)) * ((d : ℝ) * Real.log X / (X ^ ((7 : ℝ) / 20) * a * (b : ℝ) ^ 2)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        push_cast; linarith
    _ = 2 * d * Real.log X * X ^ ((1 : ℝ) / 60) / ((a : ℝ) * (b : ℝ) ^ 2) := by
        have h11 : X ^ ((11 : ℝ) / 30) = X ^ ((1 : ℝ) / 60) * X ^ ((7 : ℝ) / 20) := by
          rw [rpow_mul_rpow hX0]; norm_num
        rw [h11]
        field_simp

theorem aliquot_le_sq (n : ℕ) : aliquot n ≤ n ^ 2 :=
  le_trans (Nat.sub_le _ _) (sig_le_sq n)

open Classical in
/-- The `(h, q)`-sums for fixed `(q', ℓ)`. -/
theorem lh_inner_ab (X : ℝ) (hX1 : 1 ≤ X) (d : ℕ) (hL : 0 ≤ Real.log X) (Cε : ℝ) (hCε : 0 ≤ Cε)
    (hτ : ∀ m : ℕ, 1 ≤ m → (m.divisors.card : ℝ) ≤ Cε * (m : ℝ) ^ ((1 : ℝ) / 120))
    (NQ NL NH a b : ℕ) (ha : 1 ≤ a) (haN : a ≤ NQ) (hb : 1 ≤ b) (hbN : b ≤ NL)
    (hNQ : (NQ : ℝ) ≤ X ^ ((11 : ℝ) / 30)) (hNL : (NL : ℝ) ≤ X ^ ((1 : ℝ) / 10)) :
    ∑ c ∈ Finset.Icc 1 NH, ∑ e ∈ Finset.Icc 1 NQ,
        (if lhCond X (a, b, c, e) then lhG X d (a, b, c, e) else 0) ≤
      Cε * X ^ ((1 : ℝ) / 120) * (2 * d * Real.log X * X ^ ((1 : ℝ) / 60)) /
        X ^ ((3 : ℝ) / 40) / ((a : ℝ) * b) := by
  classical
  have hX0 : 0 < X := by linarith
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb
  have h3 : 0 < X ^ ((3 : ℝ) / 40) := Real.rpow_pos_of_pos hX0 _
  have hRHS : 0 ≤ Cε * X ^ ((1 : ℝ) / 120) * (2 * d * Real.log X * X ^ ((1 : ℝ) / 60)) /
      X ^ ((3 : ℝ) / 40) / ((a : ℝ) * b) := by positivity
  by_cases hB : X ^ ((3 : ℝ) / 40) < (b : ℝ)
  · set m := aliquot (a * b) with hm
    have hb2 : 2 ≤ b := by
      have : (1 : ℝ) < b := lt_of_le_of_lt (Real.one_le_rpow hX1 (by norm_num)) hB
      exact_mod_cast this
    have hm1 : 1 ≤ m := one_le_aliquot (le_trans hb2 (Nat.le_mul_of_pos_left b ha))
    set W : ℝ := 2 * d * Real.log X * X ^ ((1 : ℝ) / 60) / ((a : ℝ) * (b : ℝ) ^ 2) with hW
    have hW0 : 0 ≤ W := by rw [hW]; positivity
    -- each `c`
    have hc_le : ∀ c ∈ Finset.Icc 1 NH, ∑ e ∈ Finset.Icc 1 NQ,
        (if lhCond X (a, b, c, e) then lhG X d (a, b, c, e) else 0) ≤ if c ∣ m then W else 0 := by
      intro c hc
      have hc1 : 1 ≤ c := (Finset.mem_Icc.1 hc).1
      by_cases hcm : c ∣ m ∧ X ^ ((10 : ℝ) / 33) < (c : ℝ)
      · rw [if_pos hcm.1]
        have := lh_inner_q X hX0 d hL NQ a b c hc1 ha haN hb hNQ
        refine le_trans (le_of_eq ?_) this
        refine Finset.sum_congr rfl (fun e _ => ?_)
        unfold lhCond
        simp only
        by_cases h1 : e ≡ a [MOD c] ∧ e ≠ a ∧ X ^ ((7 : ℝ) / 20) < (e : ℝ)
        · rw [if_pos h1, if_pos ⟨hB, hcm.1, hcm.2, h1⟩]
        · rw [if_neg h1, if_neg (fun h => h1 h.2.2.2)]
      · have h0 : ∑ e ∈ Finset.Icc 1 NQ,
            (if lhCond X (a, b, c, e) then lhG X d (a, b, c, e) else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro e _
          rw [if_neg]
          intro h
          exact hcm ⟨h.2.1, h.2.2.1⟩
        rw [h0]
        split_ifs <;> simp [hW0]
    calc _ ≤ ∑ c ∈ Finset.Icc 1 NH, (if c ∣ m then W else 0) := Finset.sum_le_sum hc_le
      _ = ((Finset.Icc 1 NH).filter (fun c => c ∣ m)).card * W := by
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      _ ≤ (m.divisors.card : ℝ) * W := by
          apply mul_le_mul_of_nonneg_right _ hW0
          have : (Finset.Icc 1 NH).filter (fun c => c ∣ m) ⊆ m.divisors := by
            intro c hc
            rw [Finset.mem_filter] at hc
            exact Nat.mem_divisors.2 ⟨hc.2, by omega⟩
          exact_mod_cast Finset.card_le_card this
      _ ≤ (Cε * X ^ ((1 : ℝ) / 120)) * W := by
          apply mul_le_mul_of_nonneg_right _ hW0
          refine le_trans (hτ m hm1) (mul_le_mul_of_nonneg_left ?_ hCε)
          apply Real.rpow_le_rpow (Nat.cast_nonneg _) _ (by norm_num)
          have hmab : (m : ℝ) ≤ ((a * b : ℕ) : ℝ) ^ 2 := by exact_mod_cast aliquot_le_sq (a * b)
          have hab : ((a * b : ℕ) : ℝ) ≤ X ^ ((11 : ℝ) / 30) * X ^ ((1 : ℝ) / 10) := by
            push_cast
            have h1 : (a : ℝ) ≤ X ^ ((11 : ℝ) / 30) :=
              le_trans (by exact_mod_cast haN) hNQ
            have h2 : (b : ℝ) ≤ X ^ ((1 : ℝ) / 10) := le_trans (by exact_mod_cast hbN) hNL
            exact mul_le_mul h1 h2 hb0.le (Real.rpow_nonneg hX0.le _)
          have hX7 : X ^ ((11 : ℝ) / 30) * X ^ ((1 : ℝ) / 10) = X ^ ((7 : ℝ) / 15) := by
            rw [rpow_mul_rpow hX0]; norm_num
          rw [hX7] at hab
          have hsq : (X ^ ((7 : ℝ) / 15)) ^ 2 ≤ X := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hX0.le]
            calc X ^ ((7 : ℝ) / 15 * ((2 : ℕ) : ℝ)) ≤ X ^ (1 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num)
              _ = X := Real.rpow_one X
          have : ((a * b : ℕ) : ℝ) ^ 2 ≤ (X ^ ((7 : ℝ) / 15)) ^ 2 :=
            pow_le_pow_left₀ (Nat.cast_nonneg _) hab 2
          linarith
      _ ≤ Cε * X ^ ((1 : ℝ) / 120) * (2 * d * Real.log X * X ^ ((1 : ℝ) / 60)) /
            X ^ ((3 : ℝ) / 40) / ((a : ℝ) * b) := by
          rw [hW]
          have hbb : (1 : ℝ) / (b : ℝ) ^ 2 ≤ 1 / (X ^ ((3 : ℝ) / 40) * b) := by
            apply one_div_le_one_div_of_le (by positivity)
            rw [sq]
            exact mul_le_mul_of_nonneg_right hB.le hb0.le
          have hK : 0 ≤ Cε * X ^ ((1 : ℝ) / 120) * (2 * d * Real.log X * X ^ ((1 : ℝ) / 60)) / a := by
            positivity
          calc Cε * X ^ ((1 : ℝ) / 120) *
                (2 * d * Real.log X * X ^ ((1 : ℝ) / 60) / ((a : ℝ) * (b : ℝ) ^ 2))
              = (Cε * X ^ ((1 : ℝ) / 120) * (2 * d * Real.log X * X ^ ((1 : ℝ) / 60)) / a) *
                  (1 / (b : ℝ) ^ 2) := by field_simp
            _ ≤ (Cε * X ^ ((1 : ℝ) / 120) * (2 * d * Real.log X * X ^ ((1 : ℝ) / 60)) / a) *
                  (1 / (X ^ ((3 : ℝ) / 40) * b)) := mul_le_mul_of_nonneg_left hbb hK
            _ = Cε * X ^ ((1 : ℝ) / 120) * (2 * d * Real.log X * X ^ ((1 : ℝ) / 60)) /
                  X ^ ((3 : ℝ) / 40) / ((a : ℝ) * b) := by field_simp
  · have h0 : ∀ c ∈ Finset.Icc 1 NH, ∑ e ∈ Finset.Icc 1 NQ,
        (if lhCond X (a, b, c, e) then lhG X d (a, b, c, e) else 0) = 0 := by
      intro c _
      apply Finset.sum_eq_zero
      intro e _
      rw [if_neg]
      intro h
      exact hB h.1
    rw [Finset.sum_congr rfl h0, Finset.sum_const_zero]
    exact hRHS

open Classical in
/-- The whole bounding sum. -/
theorem lh_nested (X : ℝ) (hX1 : 1 ≤ X) (d : ℕ) (Cε : ℝ) (hCε : 0 ≤ Cε)
    (hτ : ∀ m : ℕ, 1 ≤ m → (m.divisors.card : ℝ) ≤ Cε * (m : ℝ) ^ ((1 : ℝ) / 120))
    (NQ NL NH : ℕ) (hNQ : (NQ : ℝ) ≤ X ^ ((11 : ℝ) / 30)) (hNL : (NL : ℝ) ≤ X ^ ((1 : ℝ) / 10)) :
    ∑ y ∈ (lhBox NQ NL NH).filter (lhCond X), lhG X d y ≤
      Cε * X ^ ((1 : ℝ) / 120) * (2 * d * Real.log X * X ^ ((1 : ℝ) / 60)) /
        X ^ ((3 : ℝ) / 40) * ((1 + Real.log X) * (1 + Real.log X)) := by
  classical
  have hX0 : 0 < X := by linarith
  have hL : 0 ≤ Real.log X := Real.log_nonneg hX1
  set K : ℝ := Cε * X ^ ((1 : ℝ) / 120) * (2 * d * Real.log X * X ^ ((1 : ℝ) / 60)) /
    X ^ ((3 : ℝ) / 40) with hK
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have hHQ : ∑ i ∈ Finset.Icc 1 NQ, (1 : ℝ) / i ≤ 1 + Real.log X :=
    sum_inv_le_log (le_trans hNQ (Real.rpow_le_self_of_one_le hX1 (by norm_num))) hX1
  have hHL : ∑ i ∈ Finset.Icc 1 NL, (1 : ℝ) / i ≤ 1 + Real.log X :=
    sum_inv_le_log (le_trans hNL (Real.rpow_le_self_of_one_le hX1 (by norm_num))) hX1
  rw [Finset.sum_filter]
  unfold lhBox
  rw [Finset.sum_product]
  calc _ ≤ ∑ a ∈ Finset.Icc 1 NQ, K * (1 + Real.log X) * ((1 : ℝ) / a) := by
        apply Finset.sum_le_sum
        intro a ha
        obtain ⟨ha1, haN⟩ := Finset.mem_Icc.1 ha
        have ha0 : (0 : ℝ) < a := by exact_mod_cast ha1
        rw [Finset.sum_product]
        calc _ ≤ ∑ b ∈ Finset.Icc 1 NL, K / ((a : ℝ) * b) := by
              apply Finset.sum_le_sum
              intro b hb
              obtain ⟨hb1, hbN⟩ := Finset.mem_Icc.1 hb
              rw [Finset.sum_product]
              exact lh_inner_ab X hX1 d hL Cε hCε hτ NQ NL NH a b ha1 haN hb1 hbN hNQ hNL
          _ = K / a * ∑ b ∈ Finset.Icc 1 NL, (1 : ℝ) / b := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl (fun b _ => ?_)
              field_simp
          _ ≤ K / a * (1 + Real.log X) := mul_le_mul_of_nonneg_left hHL (by positivity)
          _ = K * (1 + Real.log X) * ((1 : ℝ) / a) := by field_simp
    _ = K * (1 + Real.log X) * ∑ a ∈ Finset.Icc 1 NQ, (1 : ℝ) / a := by rw [Finset.mul_sum]
    _ ≤ K * (1 + Real.log X) * (1 + Real.log X) :=
        mul_le_mul_of_nonneg_left hHQ (by positivity)
    _ = _ := by rw [hK]; ring

theorem gcd_le_add (a b : ℕ) : Nat.gcd a b ≤ a + b := by
  rcases Nat.eq_zero_or_pos a with h0 | hpos
  · rw [h0, Nat.gcd_zero_left]; omega
  · exact le_trans (Nat.gcd_le_left b hpos) (Nat.le_add_right a b)

theorem ratio32_nonneg (X : ℝ) (n n' : ℕ) : 0 ≤ SV.ratio32 X n n' := by
  classical
  unfold SV.ratio32
  apply prod_ratio_nonneg
  intro p hp
  exact (Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hp).1).one_lt.le

open Classical in
/-- Every large-`h` collision pair `(n, n')` is `(qℓ, q'ℓ)` for a quadruple `(q', ℓ, h, q)` of the
bounding box, with `gcd(s(n), s(n')) = dh` (EP1054.tex lines 1710–1727, via the rigidity
`ℓ = ℓ'`, `q ≡ q' (mod h)`); hence the reduced sum is at most the box sum of `dh log X/(qq'ℓ²)`
(using `A'_{3,2}/φ(A'_{3,2}) ≤ log X`). -/
theorem lh_cover (D : ℕ) (A : Finset ℕ) (X : ℝ) (d : ℕ) (hX1 : 1 ≤ X) (hlog : 1 ≤ Real.log X)
    (hdvd : ∀ p q r k : ℕ, SV.MemberTuple D A X d p q r k → d ∣ aliquot (q * r * k))
    (hrig : ∀ p q r k p' q' r' k' : ℕ, SV.MemberTuple D A X d p q r k →
      SV.MemberTuple D A X d p' q' r' k' → q * r * k ≠ q' * r' * k' →
      aliquot (p * q * r * k) = aliquot (p' * q' * r' * k') →
      X ^ ((10 : ℝ) / 33) < ((SV.gcdS (q * r * k) (q' * r' * k') / d : ℕ) : ℝ) →
      r * k = r' * k' ∧ q ≡ q' [MOD (SV.gcdS (q * r * k) (q' * r' * k') / d)]) :
    SV.reducedCollisionSum D A X d (fun h => X ^ ((10 : ℝ) / 33) < (h : ℝ)) ≤
      ∑ y ∈ (lhBox ⌊X ^ ((11 : ℝ) / 30)⌋₊ ⌊X ^ ((1 : ℝ) / 10)⌋₊ (2 * ⌊X⌋₊ ^ 2)).filter (lhCond X),
        lhG X d y := by
  have hX0 : 0 < X := by linarith
  have hL0 : 0 ≤ Real.log X := by linarith
  unfold SV.reducedCollisionSum
  set NQ := ⌊X ^ ((11 : ℝ) / 30)⌋₊ with hNQ
  set NL := ⌊X ^ ((1 : ℝ) / 10)⌋₊ with hNL
  set N := ⌊X⌋₊ with hN
  set T := (lhBox NQ NL (2 * N ^ 2)).filter
    (fun y => lhCond X y ∧ SV.gcdS (y.2.2.2 * y.2.1) (y.1 * y.2.1) = d * y.2.2.1) with hT
  set π : ℕ × ℕ × ℕ × ℕ → ℕ × ℕ := fun y => (y.2.2.2 * y.2.1, y.1 * y.2.1) with hπ
  set F : ℕ × ℕ → ℝ := fun nn =>
    (SV.gcdS nn.1 nn.2 : ℝ) / ((nn.1 : ℝ) * (nn.2 : ℝ)) * SV.ratio32 X nn.1 nn.2 with hF
  have hF0 : ∀ nn, 0 ≤ F nn := fun nn => by
    rw [hF]; exact mul_nonneg (by positivity) (ratio32_nonneg X _ _)
  have hsub : (Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter
      (fun nn : ℕ × ℕ => SV.CollisionPair D A X d nn.1 nn.2 ∧
        X ^ ((10 : ℝ) / 33) < ((SV.gcdS nn.1 nn.2 / d : ℕ) : ℝ)) ⊆ T.image π := by
    intro x hx
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hx
    obtain ⟨⟨⟨_, hx1N⟩, ⟨_, hx2N⟩⟩, hCP, hbig⟩ := hx
    obtain ⟨hne, p, p', ⟨q, r, k, ht, hn⟩, ⟨q', r', k', ht', hn'⟩, hcoll⟩ := hCP
    have hTt := ht.1
    have hTt' := ht'.1
    rw [hn, hn'] at hbig hcoll hne
    rw [hn] at hx1N
    rw [hn'] at hx2N
    have hcoll' : aliquot (p * q * r * k) = aliquot (p' * q' * r' * k') := by
      simpa only [mul_assoc] using hcoll
    obtain ⟨hl, hq⟩ := hrig p q r k p' q' r' k' ht ht' hne hcoll' hbig
    have hd : d ∣ SV.gcdS (q * r * k) (q' * r' * k') := Nat.dvd_gcd (hdvd _ _ _ _ ht) (hdvd _ _ _ _ ht')
    have hk := tuple_k_pos hX0.le hTt
    have hr := hTt.2.2.1.pos
    have hh1 : 1 ≤ SV.gcdS (q * r * k) (q' * r' * k') / d := by
      rcases Nat.eq_zero_or_pos (SV.gcdS (q * r * k) (q' * r' * k') / d) with h0 | h0
      · rw [h0, Nat.cast_zero] at hbig
        have := Real.rpow_pos_of_pos hX0 ((10 : ℝ) / 33)
        linarith
      · exact h0
    have hhN : SV.gcdS (q * r * k) (q' * r' * k') / d ≤ 2 * N ^ 2 := by
      calc _ ≤ SV.gcdS (q * r * k) (q' * r' * k') := Nat.div_le_self _ _
        _ ≤ aliquot (q * r * k) + aliquot (q' * r' * k') := gcd_le_add _ _
        _ ≤ (q * r * k) ^ 2 + (q' * r' * k') ^ 2 :=
            Nat.add_le_add (aliquot_le_sq _) (aliquot_le_sq _)
        _ ≤ N ^ 2 + N ^ 2 := Nat.add_le_add (Nat.pow_le_pow_left hx1N 2) (Nat.pow_le_pow_left hx2N 2)
        _ = 2 * N ^ 2 := by ring
    have hqq : q ≠ q' := by
      intro h
      apply hne
      rw [mul_assoc, mul_assoc q', ← hl, h]
    refine Finset.mem_image.2 ⟨(q', r * k, SV.gcdS (q * r * k) (q' * r' * k') / d, q), ?_, ?_⟩
    · rw [hT, Finset.mem_filter]
      refine ⟨?_, ⟨?_, ?_, hbig, hq, hqq, tuple_q_gt hTt⟩, ?_⟩
      · unfold lhBox
        simp only [Finset.mem_product, Finset.mem_Icc]
        exact ⟨⟨hTt'.2.1.one_lt.le, Nat.le_floor (tuple_q_le hTt')⟩,
          ⟨Nat.mul_pos hr hk, Nat.le_floor (tuple_l_le hX1 hTt)⟩, ⟨hh1, hhN⟩,
          ⟨hTt.2.1.one_lt.le, Nat.le_floor (tuple_q_le hTt)⟩⟩
      · exact tuple_l_gt hX1 hTt
      · show SV.gcdS (q * r * k) (q' * r' * k') / d ∣ aliquot (q' * (r * k))
        rw [hl, ← mul_assoc]
        exact (Nat.div_dvd_of_dvd hd).trans (Nat.gcd_dvd_right _ _)
      · show SV.gcdS (q * (r * k)) (q' * (r * k)) = d * (SV.gcdS (q * r * k) (q' * r' * k') / d)
        rw [← mul_assoc, hl, ← mul_assoc]
        exact (Nat.mul_div_cancel' hd).symm
    · refine Prod.ext ?_ ?_
      · show q * (r * k) = x.1
        rw [hn, mul_assoc]
      · show q' * (r * k) = x.2
        rw [hn', hl, mul_assoc]
  calc ∑ nn ∈ (Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter
          (fun nn : ℕ × ℕ => SV.CollisionPair D A X d nn.1 nn.2 ∧
            X ^ ((10 : ℝ) / 33) < ((SV.gcdS nn.1 nn.2 / d : ℕ) : ℝ)), F nn
        ≤ ∑ nn ∈ T.image π, F nn :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => hF0 i)
    _ ≤ ∑ y ∈ T, F (π y) := Finset.sum_image_le_of_nonneg (fun u _ => hF0 u)
    _ ≤ ∑ y ∈ T, lhG X d y := by
        apply Finset.sum_le_sum
        intro y hy
        rw [hT, Finset.mem_filter] at hy
        obtain ⟨-, -, hΨ⟩ := hy
        rw [hF, hπ]
        simp only
        rw [hΨ]
        unfold lhG
        push_cast
        have hr := ratio32_le_log X hlog (y.2.2.2 * y.2.1) (y.1 * y.2.1)
        calc (d : ℝ) * y.2.2.1 / ((y.2.2.2 : ℝ) * y.2.1 * ((y.1 : ℝ) * y.2.1)) *
              SV.ratio32 X (y.2.2.2 * y.2.1) (y.1 * y.2.1)
            ≤ (d : ℝ) * y.2.2.1 / ((y.2.2.2 : ℝ) * y.2.1 * ((y.1 : ℝ) * y.2.1)) * Real.log X :=
              mul_le_mul_of_nonneg_left hr (by positivity)
          _ = (d : ℝ) * y.2.2.1 * Real.log X / ((y.2.2.2 : ℝ) * y.1 * (y.2.1 : ℝ) ^ 2) := by ring
    _ ≤ _ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro y hy
          rw [hT, Finset.mem_filter] at hy
          rw [Finset.mem_filter]
          exact ⟨hy.1, hy.2.1⟩
        · intro y _ _
          exact lhG_nonneg X hL0 d y

/-- The final real inequality of the large-`h` case. -/
theorem lh_final {X L lY W d Cε c ε : ℝ} (hX : 0 < X) (hL : 1 ≤ L) (hlY : 0 < lY)
    (hlYL : lY ≤ L) (hW : 0 < W) (hd : 1 ≤ d) (hdL : d ≤ L ^ c) (hCε : 0 ≤ Cε) (hε : 0 < ε)
    (hasym : 8 * Cε * ((L ^ c) ^ 2 * L ^ 4) ≤ ε * W) :
    X * lY / L ^ 2 * (Cε * 2 * d * L * ((1 + L) * (1 + L)) / W) ≤ ε * (X / (d * lY)) := by
  have hL0 : 0 < L := by linarith
  have hd0 : 0 < d := by linarith
  have key : 2 * Cε * d ^ 2 * lY ^ 2 * ((1 + L) * (1 + L)) ≤ ε * (L * W) := by
    have h1 : d ^ 2 ≤ (L ^ c) ^ 2 := pow_le_pow_left₀ hd0.le hdL 2
    have h2 : lY ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ hlY.le hlYL 2
    have h3 : (1 + L) * (1 + L) ≤ 4 * L ^ 2 := by nlinarith
    calc 2 * Cε * d ^ 2 * lY ^ 2 * ((1 + L) * (1 + L))
        ≤ 2 * Cε * (L ^ c) ^ 2 * L ^ 2 * (4 * L ^ 2) := by
          have hc1 : 0 ≤ 2 * Cε := by linarith
          have := mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left h1 hc1) h2 (by positivity)
            (by positivity)) h3 (by positivity) (by positivity)
          linarith
      _ = 8 * Cε * ((L ^ c) ^ 2 * L ^ 4) := by ring
      _ ≤ ε * W := hasym
      _ ≤ ε * (L * W) := by
          have : W ≤ L * W := by nlinarith
          exact mul_le_mul_of_nonneg_left this hε.le
  have e1 : X * lY / L ^ 2 * (Cε * 2 * d * L * ((1 + L) * (1 + L)) / W) =
      X * ((2 * Cε * d * lY * ((1 + L) * (1 + L))) / (L * W)) := by
    field_simp
  have e2 : ε * (X / (d * lY)) = X * (ε / (d * lY)) := by ring
  rw [e1, e2]
  apply mul_le_mul_of_nonneg_left _ hX.le
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [key]

theorem link_largeH : Spine.Link_Claim_SvLargeH := by
  intro hrig hdiv _hM2 δ hδ hδ1 D hD 𝒜 hreg c hc ε hε
  obtain ⟨X₁, hX₁⟩ := hrig δ hδ hδ1 D hD 𝒜 hreg
  obtain ⟨Cε, hCε⟩ := hdiv ((1 : ℝ) / 120) (by norm_num)
  have hCε0 : 0 ≤ Cε := by
    have := hCε 1 le_rfl
    simp at this
    linarith
  obtain ⟨c0, _, B, _, X₀, hX₀⟩ := hreg
  have hlo := (isLittleO_log_rpow_rpow_atTop (2 * c + 4) (by norm_num : (0 : ℝ) < 1 / 20)).bound
    (by positivity : (0 : ℝ) < ε / (8 * Cε + 1))
  obtain ⟨X₂, hX₂⟩ := Filter.eventually_atTop.1 hlo
  refine ⟨max (max X₀ X₁) (max X₂ (max 1 (Real.exp (120 * Real.exp 3)))), ?_⟩
  intro X hX d hd1 _hdsm hdY
  have hXa : X₀ ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hXb : X₁ ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hXc : X₂ ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hX
  have hX1 : 1 ≤ X :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hX
  have hXe : Real.exp (120 * Real.exp 3) ≤ X :=
    le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hX
  have hX0 : 0 < X := by linarith
  have hA := (hX₀ X hXa).2.2
  have hLbig : 120 * Real.exp 3 ≤ Real.log X := by
    calc 120 * Real.exp 3 = Real.log (Real.exp (120 * Real.exp 3)) := (Real.log_exp _).symm
      _ ≤ Real.log X := Real.log_le_log (Real.exp_pos _) hXe
  have he3 : 1 ≤ Real.exp 3 := by
    have := Real.add_one_le_exp 3; linarith
  have hlog1 : 1 ≤ Real.log X := by linarith
  obtain ⟨hYe, hYL⟩ := Ycut_bounds hX0 hLbig
  have he1 : 2 < Real.exp 1 := by have := Real.add_one_le_exp 1; have := Real.exp_one_gt_d9; linarith
  have hY1 : 1 < SV.Ycut X := by linarith
  have hlY : 0 < Real.log (SV.Ycut X) := Real.log_pos hY1
  have hlYL : Real.log (SV.Ycut X) ≤ Real.log X := by
    have := Real.log_le_sub_one_of_pos (by linarith : 0 < SV.Ycut X)
    linarith
  -- the covering and the box bound
  have hcov := lh_cover D (𝒜 X) X d hX1 hlog1
    (fun p q r k ht => reg_d_dvd_aliquot (member_reg hA ht).2.2.1)
    (fun p q r k p' q' r' k' ht ht' hne hcoll hh => hX₁ X hXb d p q r k p' q' r' k' ht ht' hne hcoll hh)
  have hnest := lh_nested X hX1 d Cε hCε0 hCε ⌊X ^ ((11 : ℝ) / 30)⌋₊ ⌊X ^ ((1 : ℝ) / 10)⌋₊
    (2 * ⌊X⌋₊ ^ 2) (Nat.floor_le (Real.rpow_nonneg hX0.le _))
    (Nat.floor_le (Real.rpow_nonneg hX0.le _))
  have hRS := hcov.trans hnest
  set L := Real.log X with hLdef
  set lY := Real.log (SV.Ycut X) with hlYdef
  set W := X ^ ((1 : ℝ) / 20) with hWdef
  have hW0 : 0 < W := Real.rpow_pos_of_pos hX0 _
  have hE : Cε * X ^ ((1 : ℝ) / 120) * (2 * d * L * X ^ ((1 : ℝ) / 60)) / X ^ ((3 : ℝ) / 40) *
      ((1 + L) * (1 + L)) = Cε * 2 * d * L * ((1 + L) * (1 + L)) / W := by
    have h3 : X ^ ((3 : ℝ) / 40) = X ^ ((1 : ℝ) / 120) * X ^ ((1 : ℝ) / 60) * W := by
      rw [hWdef, rpow_mul_rpow hX0, rpow_mul_rpow hX0]; norm_num
    have h1 : 0 < X ^ ((1 : ℝ) / 120) := Real.rpow_pos_of_pos hX0 _
    have h2 : 0 < X ^ ((1 : ℝ) / 60) := Real.rpow_pos_of_pos hX0 _
    rw [h3]
    field_simp
  rw [hE] at hRS
  have hdL : (d : ℝ) ≤ L ^ c :=
    le_trans hdY (Real.rpow_le_rpow (by linarith) hYL hc.le)
  have hasym : 8 * Cε * ((L ^ c) ^ 2 * L ^ 4) ≤ ε * W := by
    have h1 := hX₂ X hXc
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith) _),
      abs_of_nonneg hW0.le] at h1
    have hL0 : 0 < L := by linarith
    have hpow : L ^ (2 * c + 4) = (L ^ c) ^ 2 * L ^ 4 := by
      rw [Real.rpow_add hL0, ← Real.rpow_natCast (L ^ c) 2, ← Real.rpow_mul hL0.le,
        ← Real.rpow_natCast L 4]
      congr 1
      congr 1; push_cast; ring
    rw [hpow] at h1
    have hZ : 0 ≤ (L ^ c) ^ 2 * L ^ 4 := by positivity
    calc 8 * Cε * ((L ^ c) ^ 2 * L ^ 4) ≤ (8 * Cε + 1) * ((L ^ c) ^ 2 * L ^ 4) := by nlinarith
      _ ≤ (8 * Cε + 1) * (ε / (8 * Cε + 1) * W) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = ε * W := by field_simp
  have hpre : 0 ≤ X * lY / L ^ 2 := by positivity
  calc X * lY / L ^ 2 * SV.reducedCollisionSum D (𝒜 X) X d
        (fun h => X ^ ((10 : ℝ) / 33) < (h : ℝ))
      ≤ X * lY / L ^ 2 * (Cε * 2 * d * L * ((1 + L) * (1 + L)) / W) :=
        mul_le_mul_of_nonneg_left hRS hpre
    _ ≤ ε * (X / (d * lY)) :=
        lh_final hX0 hlog1 hlY hlYL hW0 (by exact_mod_cast hd1) hdL hCε0 hε hasym

/-! ## The sieve bound for a fixed collision pair -/

/-- Linear Diophantine parametrization: if `x A₁ = y A₂` with `gcd(A₁, A₂) = 1` and `A₂ > 0`,
then `x = A₂ t`, `y = A₁ t` with `t = x / A₂`. -/
theorem lin_param {A1 A2 : ℕ} (hcop : Nat.Coprime A1 A2) (hA2 : 0 < A2) {x y : ℤ}
    (h : x * A1 = y * A2) : (A2 : ℤ) * (x / A2) = x ∧ y = A1 * (x / A2) := by
  have hc : IsCoprime (A2 : ℤ) (A1 : ℤ) := Nat.isCoprime_iff_coprime.2 hcop.symm
  have hdvd : (A2 : ℤ) ∣ x := hc.dvd_of_dvd_mul_right ⟨y, by rw [h]; ring⟩
  have e1 : (A2 : ℤ) * (x / A2) = x := Int.mul_ediv_cancel' hdvd
  refine ⟨e1, ?_⟩
  have hA2' : (A2 : ℤ) ≠ 0 := by exact_mod_cast hA2.ne'
  apply mul_right_cancel₀ hA2'
  calc y * A2 = x * A1 := h.symm
    _ = (A2 : ℤ) * (x / A2) * A1 := by rw [e1]
    _ = A1 * (x / A2) * A2 := by ring

/-- The facts carried by an `n`-part (for `X ≥ 2^15`). -/
theorem npart_facts {D : ℕ} {A : Finset ℕ} {X : ℝ} {d p n : ℕ} (hX15 : 2 ^ 15 ≤ X)
    (h : SV.IsNPart D A X d p n) :
    p.Prime ∧ ¬ p ∣ n ∧ X / (2 * (n : ℝ)) < p ∧ (p : ℝ) ≤ X / n ∧ 0 < n ∧
      (n : ℝ) ≤ X ^ ((7 : ℝ) / 15) := by
  obtain ⟨q, r, k, ht, rfl⟩ := h
  have hT := ht.1
  have hX1 : 1 ≤ X := by linarith
  refine ⟨hT.1, tuple_p_not_dvd hX15 hT, ?_, ?_, tuple_n_pos hX1 hT, tuple_n_le hX1 hT⟩
  · obtain ⟨-, -, -, -, -, -, -, -, -, -, hp1, -⟩ := hT
    have e : (2 * (q : ℝ) * r * k) = 2 * ((q * r * k : ℕ) : ℝ) := by push_cast; ring
    rw [e] at hp1; exact hp1
  · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hp2⟩ := hT
    have e : ((q : ℝ) * r * k) = ((q * r * k : ℕ) : ℝ) := by push_cast; ring
    rw [e] at hp2; exact hp2


theorem npart_lin {D : ℕ} {A : Finset ℕ} {X : ℝ} {d p₁ p₂ n n' : ℕ} (hX15 : 2 ^ 15 ≤ X)
    (h1 : SV.IsNPart D A X d p₁ n) (h2 : SV.IsNPart D A X d p₂ n')
    (h3 : aliquot (p₁ * n) = aliquot (p₂ * n')) :
    (p₁ : ℤ) * aliquot n + sig n = (p₂ : ℤ) * aliquot n' + sig n' := by
  have f1 := npart_facts hX15 h1
  have f2 := npart_facts hX15 h2
  have e := (aliquot_prime_mul p₁ n f1.1 f1.2.1).symm.trans
    (h3.trans (aliquot_prime_mul p₂ n' f2.1 f2.2.1))
  exact_mod_cast e

/-- The injection of prime pairs `(p, p')` into the sieved parameters `t`
(`p = p₀ + A₂ t`, `p' = p'₀ + A₁ t`; EP1054.tex lines 1588–1596). -/
theorem sieve_inj {A1 A2 : ℕ} (hcop : Nat.Coprime A1 A2) (hA2 : 0 < A2) (p₀ p₀' : ℤ)
    (lo L : ℝ) (P : Finset (ℕ × ℕ))
    (hP : ∀ pp ∈ P, ((pp.1 : ℤ) - p₀) * A1 = ((pp.2 : ℤ) - p₀') * A2 ∧ pp.1.Prime ∧ pp.2.Prime ∧
      lo < (pp.1 : ℝ) ∧ (pp.1 : ℝ) ≤ lo + L) :
    P.card ≤ ((Finset.Icc ⌈(lo - p₀) / A2⌉ (⌈(lo - p₀) / A2⌉ + ⌊L / A2⌋)).filter
      (fun t : ℤ => ((A2 : ℤ) * t + p₀).toNat.Prime ∧ ((A1 : ℤ) * t + p₀').toNat.Prime)).card := by
  have hA2R : (0 : ℝ) < A2 := by exact_mod_cast hA2
  have key : ∀ pp ∈ P, (A2 : ℤ) * (((pp.1 : ℤ) - p₀) / A2) + p₀ = pp.1 ∧
      (A1 : ℤ) * (((pp.1 : ℤ) - p₀) / A2) + p₀' = pp.2 := by
    intro pp hpp
    obtain ⟨e1, e2⟩ := lin_param hcop hA2 (hP pp hpp).1
    exact ⟨by linear_combination e1, by linear_combination -e2⟩
  apply Finset.card_le_card_of_injOn (fun pp : ℕ × ℕ => ((pp.1 : ℤ) - p₀) / A2)
  · intro pp hpp
    have hpp' : pp ∈ P := hpp
    obtain ⟨e1, e2⟩ := key pp hpp'
    obtain ⟨-, hp1, hp2, hlo, hhi⟩ := hP pp hpp'
    rw [Finset.coe_filter]
    simp only
    set t : ℤ := ((pp.1 : ℤ) - p₀) / A2 with htdef
    have htR : (A2 : ℝ) * t + p₀ = pp.1 := by exact_mod_cast e1
    have ht_eq : (t : ℝ) = ((pp.1 : ℝ) - p₀) / A2 := by
      rw [eq_div_iff hA2R.ne']; linarith
    refine ⟨Finset.mem_coe.2 (Finset.mem_Icc.2 ⟨?_, ?_⟩), ?_, ?_⟩
    · rw [Int.ceil_le, ht_eq]
      exact div_le_div_of_nonneg_right (by linarith) hA2R.le
    · have h1' : (t : ℝ) ≤ (lo - p₀) / A2 + L / A2 := by
        rw [ht_eq, ← add_div]
        exact div_le_div_of_nonneg_right (by linarith) hA2R.le
      have h2' : (lo - p₀) / A2 ≤ ((⌈(lo - p₀) / A2⌉ : ℤ) : ℝ) := Int.le_ceil _
      have : t - ⌈(lo - p₀) / A2⌉ ≤ ⌊L / A2⌋ := by
        rw [Int.le_floor]; push_cast; linarith
      linarith
    · rw [e1]; exact hp1
    · rw [e2]; exact hp2
  · intro pp hpp pp' hpp' heq
    obtain ⟨e1, e2⟩ := key pp hpp
    obtain ⟨e1', e2'⟩ := key pp' hpp'
    simp only at heq
    rw [heq] at e1 e2
    have k1 : (pp.1 : ℤ) = pp'.1 := e1.symm.trans e1'
    have k2 : (pp.2 : ℤ) = pp'.2 := e2.symm.trans e2'
    exact Prod.ext (by exact_mod_cast k1) (by exact_mod_cast k2)

/-- The size of the `t`-interval: `X^{1/30} ≤ T ≤ Xg/(nn')` for `T = (X/2n)/A₂`. -/
theorem sieve_T_bounds {X δ Cδ n n' g A2 : ℝ} (hX0 : 0 < X) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hn : 0 < n) (hn' : 0 < n') (hnle : n ≤ X ^ ((7 : ℝ) / 15)) (hn'le : n' ≤ X ^ ((7 : ℝ) / 15))
    (hg : 0 < g) (hA2 : 0 < A2) (hA2le : A2 ≤ Cδ * n') (hCδ : 0 ≤ Cδ)
    (hA2low : n' / δ ≤ g * A2) (hX30 : 2 * Cδ + 2 ≤ X ^ ((1 : ℝ) / 30)) :
    X ^ ((1 : ℝ) / 30) ≤ X / (2 * n) / A2 ∧ X / (2 * n) / A2 ≤ X * g / (n * n') := by
  have h7 : 0 < X ^ ((7 : ℝ) / 15) := Real.rpow_pos_of_pos hX0 _
  have h30 : 0 < X ^ ((1 : ℝ) / 30) := Real.rpow_pos_of_pos hX0 _
  have eT : X / (2 * n) / A2 = X / (2 * n * A2) := by rw [div_div]
  rw [eT]
  constructor
  · have hA2le' : A2 ≤ Cδ * X ^ ((7 : ℝ) / 15) :=
      le_trans hA2le (mul_le_mul_of_nonneg_left hn'le hCδ)
    have hden : 2 * n * A2 ≤ 2 * X ^ ((7 : ℝ) / 15) * (Cδ * X ^ ((7 : ℝ) / 15)) := by
      have := mul_le_mul hnle hA2le' hA2.le h7.le
      linarith
    have hX1eq : X = X ^ ((1 : ℝ) / 30) * X ^ ((1 : ℝ) / 30) * X ^ ((7 : ℝ) / 15) *
        X ^ ((7 : ℝ) / 15) := by
      rw [rpow_mul_rpow hX0, rpow_mul_rpow hX0, rpow_mul_rpow hX0]; norm_num
    rw [le_div_iff₀ (by positivity)]
    calc X ^ ((1 : ℝ) / 30) * (2 * n * A2)
        ≤ X ^ ((1 : ℝ) / 30) * (2 * X ^ ((7 : ℝ) / 15) * (Cδ * X ^ ((7 : ℝ) / 15))) :=
          mul_le_mul_of_nonneg_left hden h30.le
      _ = X ^ ((1 : ℝ) / 30) * (2 * Cδ) * X ^ ((7 : ℝ) / 15) * X ^ ((7 : ℝ) / 15) := by ring
      _ ≤ X ^ ((1 : ℝ) / 30) * X ^ ((1 : ℝ) / 30) * X ^ ((7 : ℝ) / 15) * X ^ ((7 : ℝ) / 15) := by
          gcongr; linarith
      _ = X := hX1eq.symm
  · rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : X * (n * n') ≤ X * (n * (δ * (g * A2))) := by
      apply mul_le_mul_of_nonneg_left _ hX0.le
      apply mul_le_mul_of_nonneg_left _ hn.le
      rw [div_le_iff₀ hδ] at hA2low
      linarith
    have h2 : X * (n * (δ * (g * A2))) ≤ X * g * (2 * n * A2) := by
      have hy : 0 ≤ g * A2 := by positivity
      have : δ * (g * A2) ≤ 2 * (g * A2) := mul_le_mul_of_nonneg_right (by linarith) hy
      calc X * (n * (δ * (g * A2))) ≤ X * (n * (2 * (g * A2))) := by
            apply mul_le_mul_of_nonneg_left _ hX0.le
            exact mul_le_mul_of_nonneg_left this hn.le
        _ = X * g * (2 * n * A2) := by ring
    linarith

/-- From the sieve bound in `T` to the bound in `X`. -/
theorem sieve_final {X T B Cs R : ℝ} (hX : 1 < X) (hT : X ^ ((1 : ℝ) / 30) ≤ T) (hTB : T ≤ B)
    (hR : 0 ≤ R) :
    Cs * T / Real.log T ^ 2 * R ≤ 900 * max Cs 0 * (B / Real.log X ^ 2) * R := by
  have hX0 : 0 < X := by linarith
  have hlogX : 0 < Real.log X := Real.log_pos hX
  have hlogT : Real.log X / 30 ≤ Real.log T := by
    have := Real.log_le_log (Real.rpow_pos_of_pos hX0 _) hT
    rw [Real.log_rpow hX0] at this
    linarith
  have hlT : 0 < Real.log T := by linarith [div_pos hlogX (by norm_num : (0 : ℝ) < 30)]
  have hT0 : 0 < T := lt_of_lt_of_le (Real.rpow_pos_of_pos hX0 _) hT
  have hTT : T / Real.log T ^ 2 ≤ 900 * (B / Real.log X ^ 2) := by
    rw [div_le_iff₀ (by positivity)]
    have hsq : (Real.log X) ^ 2 / 900 ≤ Real.log T ^ 2 := by
      have h0 : 0 ≤ Real.log X / 30 := by positivity
      nlinarith
    have hB0 : 0 ≤ B := by linarith
    have e : 900 * (B / Real.log X ^ 2) * (Real.log X ^ 2 / 900) ≤
        900 * (B / Real.log X ^ 2) * Real.log T ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    have e2 : 900 * (B / Real.log X ^ 2) * (Real.log X ^ 2 / 900) = B := by
      field_simp
    linarith
  calc Cs * T / Real.log T ^ 2 * R = (Cs * (T / Real.log T ^ 2)) * R := by ring
    _ ≤ (max Cs 0 * (T / Real.log T ^ 2)) * R := by
        apply mul_le_mul_of_nonneg_right _ hR
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    _ ≤ (max Cs 0 * (900 * (B / Real.log X ^ 2))) * R := by
        apply mul_le_mul_of_nonneg_right _ hR
        exact mul_le_mul_of_nonneg_left hTT (le_max_right _ _)
    _ = 900 * max Cs 0 * (B / Real.log X ^ 2) * R := by ring

theorem link_sievePairs : Spine.Link_Claim_SvSievePairs := by
  intro hsd _hcol hTS hsieve δ hδ hδ1 D hD 𝒜 hreg
  obtain ⟨X₁, hX₁⟩ := hsd δ hδ hδ1 D hD 𝒜 hreg
  obtain ⟨Cδ, hCδ, X₃, hX₃⟩ := hTS δ hδ hδ1 D hD
  obtain ⟨Cs, hCs⟩ := hsieve
  refine ⟨900 * max Cs 0, max (max X₁ X₃) (max (2 ^ 15) ((2 * Cδ + 2) ^ 30)), ?_⟩
  intro X hX d n n' hpair
  have hXa : X₁ ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hXb : X₃ ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hX15 : 2 ^ 15 ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hX
  have hXC : (2 * Cδ + 2) ^ 30 ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hX
  have hX1 : 1 < X := by linarith
  have hX0 : 0 < X := by linarith
  have hX30 : 2 * Cδ + 2 ≤ X ^ ((1 : ℝ) / 30) := by
    have := le_rpow_inv (n := 30) (by norm_num) (by linarith) hXC
    simpa using this
  have hσ := hX₁ X hXa d n n' hpair
  obtain ⟨_hne, p₀, p₀', hN0, hN0', hcoll0⟩ := hpair
  have hnf := npart_facts hX15 hN0
  have hnf' := npart_facts hX15 hN0'
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnf.2.2.2.2.1
  have hn'R : (0 : ℝ) < n' := by exact_mod_cast hnf'.2.2.2.2.1
  -- `λ n < s(n) < C_δ n`
  have hrat : ∀ p m : ℕ, SV.IsNPart D (𝒜 X) X d p m →
      1 / δ * (m : ℝ) < (aliquot m : ℝ) ∧ (aliquot m : ℝ) < Cδ * m := by
    intro p m hm
    obtain ⟨q, r, k, ht, rfl⟩ := hm
    have hT := ht.1
    have h := hX₃ X hXb p q r k hT (q * r * k) (Or.inr (Or.inr (Or.inl rfl)))
    exact ⟨aliquot_gt_of_ratio (tuple_n_pos hX1.le hT) h.1,
      aliquot_lt_of_ratio (tuple_n_pos hX1.le hT) h.2⟩
  obtain ⟨hsn1, -⟩ := hrat p₀ n hN0
  obtain ⟨hsn1', hsn2'⟩ := hrat p₀' n' hN0'
  have hδinv : 0 < 1 / δ := by positivity
  have hs0 : 0 < aliquot n := by
    have : (0 : ℝ) < aliquot n := lt_of_le_of_lt (by positivity) hsn1
    exact_mod_cast this
  have hs0' : 0 < aliquot n' := by
    have : (0 : ℝ) < aliquot n' := lt_of_le_of_lt (by positivity) hsn1'
    exact_mod_cast this
  -- `g = gcd(s(n), s(n'))`, `A₁ = s(n)/g`, `A₂ = s(n')/g`
  have hg0 : 0 < SV.gcdS n n' := Nat.gcd_pos_of_pos_left _ hs0
  have hA1 : SV.gcdS n n' * (aliquot n / SV.gcdS n n') = aliquot n :=
    Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
  have hA2 : SV.gcdS n n' * (aliquot n' / SV.gcdS n n') = aliquot n' :=
    Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
  have hA1pos : 0 < aliquot n / SV.gcdS n n' := Nat.div_pos (Nat.gcd_le_left _ hs0) hg0
  have hA2pos : 0 < aliquot n' / SV.gcdS n n' := Nat.div_pos (Nat.gcd_le_right _ hs0') hg0
  have hcop : Nat.Coprime (aliquot n / SV.gcdS n n') (aliquot n' / SV.gcdS n n') :=
    Nat.coprime_div_gcd_div_gcd hg0
  have E0 := npart_lin hX15 hN0 hN0' hcoll0
  have hA1Z : (SV.gcdS n n' : ℤ) * (aliquot n / SV.gcdS n n' : ℕ) = aliquot n := by
    exact_mod_cast hA1
  have hA2Z : (SV.gcdS n n' : ℤ) * (aliquot n' / SV.gcdS n n' : ℕ) = aliquot n' := by
    exact_mod_cast hA2
  -- the determinant
  have hgdet : (SV.gcdS n n' : ℤ) * (((aliquot n' / SV.gcdS n n' : ℕ) : ℤ) * p₀' -
      ((aliquot n / SV.gcdS n n' : ℕ) : ℤ) * p₀) = (sig n : ℤ) - sig n' := by
    linear_combination (p₀' : ℤ) * hA2Z - (p₀ : ℤ) * hA1Z - E0
  have hdet0 : ((aliquot n' / SV.gcdS n n' : ℕ) : ℤ) * p₀' -
      ((aliquot n / SV.gcdS n n' : ℕ) : ℤ) * p₀ ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hgdet
    apply hσ
    have : (sig n : ℤ) = sig n' := by linarith
    exact_mod_cast this
  have hdetA3 : (((aliquot n' / SV.gcdS n n' : ℕ) : ℤ) * p₀' -
      ((aliquot n / SV.gcdS n n' : ℕ) : ℤ) * p₀).natAbs = SV.A3 n n' := by
    unfold SV.A3
    rw [← hgdet, Int.natAbs_mul, Int.natAbs_natCast]
    exact (Nat.mul_div_cancel_left _ hg0).symm
  -- the length of the `t`-interval
  have hA2R : (0 : ℝ) < (aliquot n' / SV.gcdS n n' : ℕ) := by exact_mod_cast hA2pos
  have hgR : (0 : ℝ) < SV.gcdS n n' := by exact_mod_cast hg0
  have hA2cast : (SV.gcdS n n' : ℝ) * (aliquot n' / SV.gcdS n n' : ℕ) = aliquot n' := by
    exact_mod_cast hA2
  have hA2le : ((aliquot n' / SV.gcdS n n' : ℕ) : ℝ) ≤ Cδ * n' := by
    have : ((aliquot n' / SV.gcdS n n' : ℕ) : ℝ) ≤ aliquot n' := by
      have h1 : 1 ≤ (SV.gcdS n n' : ℝ) := by exact_mod_cast hg0
      nlinarith
    linarith
  have hA2low : (n' : ℝ) / δ ≤ SV.gcdS n n' * (aliquot n' / SV.gcdS n n' : ℕ) := by
    rw [hA2cast]
    have : (n' : ℝ) / δ = 1 / δ * n' := by ring
    linarith
  obtain ⟨hTlow, hTup⟩ := sieve_T_bounds hX0 hδ hδ1 hnR hn'R hnf.2.2.2.2.2 hnf'.2.2.2.2.2 hgR hA2R
    hA2le hCδ.le hA2low hX30
  have hs := hCs (aliquot n' / SV.gcdS n n') (aliquot n / SV.gcdS n n') (p₀ : ℤ) (p₀' : ℤ)
    hA2pos hA1pos hcop.symm hdet0 ⌈(X / (2 * n) - p₀) / (aliquot n' / SV.gcdS n n' : ℕ)⌉
    (X / (2 * n) / (aliquot n' / SV.gcdS n n' : ℕ)) (le_trans (by linarith) hTlow)
  rw [hdetA3] at hs
  have hcard : SV.pairCount D (𝒜 X) X d n n' ≤
      ((Finset.Icc ⌈(X / (2 * n) - p₀) / (aliquot n' / SV.gcdS n n' : ℕ)⌉
        (⌈(X / (2 * n) - p₀) / (aliquot n' / SV.gcdS n n' : ℕ)⌉ +
          ⌊X / (2 * n) / (aliquot n' / SV.gcdS n n' : ℕ)⌋)).filter
        (fun t : ℤ => (((aliquot n' / SV.gcdS n n' : ℕ) : ℤ) * t + p₀).toNat.Prime ∧
          (((aliquot n / SV.gcdS n n' : ℕ) : ℤ) * t + p₀').toNat.Prime)).card := by
    classical
    unfold SV.pairCount
    apply sieve_inj hcop hA2pos p₀ p₀' (X / (2 * n)) (X / (2 * n))
    intro pp hpp
    obtain ⟨-, h1, h2, h3⟩ := Finset.mem_filter.1 hpp
    have E1 := npart_lin hX15 h1 h2 h3
    have f1 := npart_facts hX15 h1
    have f2 := npart_facts hX15 h2
    refine ⟨?_, f1.1, f2.1, f1.2.2.1, ?_⟩
    · have hgZ : (SV.gcdS n n' : ℤ) ≠ 0 := by exact_mod_cast hg0.ne'
      apply mul_left_cancel₀ hgZ
      linear_combination (↑pp.1 - ↑p₀) * hA1Z - (↑pp.2 - ↑p₀') * hA2Z + E1 - E0
    · have : X / (n : ℝ) = X / (2 * n) + X / (2 * n) := by field_simp; ring
      linarith [f1.2.2.2.1]
  have hR0 : ∀ m : ℕ, 0 ≤ SV.phiRatio m := fun m => by unfold SV.phiRatio; positivity
  have hRR : 0 ≤ SV.phiRatio (aliquot n' / SV.gcdS n n') * SV.phiRatio (aliquot n / SV.gcdS n n') *
      SV.phiRatio (SV.A3 n n') := by
    have := hR0 (aliquot n' / SV.gcdS n n'); have := hR0 (aliquot n / SV.gcdS n n')
    have := hR0 (SV.A3 n n'); positivity
  have hfin := sieve_final (Cs := Cs) hX1 hTlow hTup hRR
  calc (SV.pairCount D (𝒜 X) X d n n' : ℝ)
      ≤ Cs * (X / (2 * n) / (aliquot n' / SV.gcdS n n' : ℕ)) /
          Real.log (X / (2 * n) / (aliquot n' / SV.gcdS n n' : ℕ)) ^ 2 *
          SV.phiRatio (aliquot n' / SV.gcdS n n') * SV.phiRatio (aliquot n / SV.gcdS n n') *
          SV.phiRatio (SV.A3 n n') := le_trans (by exact_mod_cast hcard) hs
    _ = Cs * (X / (2 * n) / (aliquot n' / SV.gcdS n n' : ℕ)) /
          Real.log (X / (2 * n) / (aliquot n' / SV.gcdS n n' : ℕ)) ^ 2 *
          (SV.phiRatio (aliquot n' / SV.gcdS n n') * SV.phiRatio (aliquot n / SV.gcdS n n') *
          SV.phiRatio (SV.A3 n n')) := by ring
    _ ≤ 900 * max Cs 0 * (X * SV.gcdS n n' / (n * n') / Real.log X ^ 2) *
          (SV.phiRatio (aliquot n' / SV.gcdS n n') * SV.phiRatio (aliquot n / SV.gcdS n n') *
          SV.phiRatio (SV.A3 n n')) := hfin
    _ = 900 * max Cs 0 * (X * (SV.gcdS n n' : ℝ) / ((n : ℝ) * (n' : ℝ) * Real.log X ^ 2)) *
          SV.phiRatio (aliquot n / SV.gcdS n n') * SV.phiRatio (aliquot n' / SV.gcdS n n') *
          SV.phiRatio (SV.A3 n n') := by
        rw [div_div]; ring

/-! ## The reduction of the `A_3` factor -/

theorem ratio_le_exp {p : ℕ} (hp : 2 ≤ p) : (p : ℝ) / ((p : ℝ) - 1) ≤ Real.exp (2 / p) := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have h1 : (p : ℝ) / ((p : ℝ) - 1) ≤ 1 + 2 / p := by
    rw [div_le_iff₀ (by linarith)]
    have h2 : 2 / (p : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    have e : (1 + 2 / (p : ℝ)) * ((p : ℝ) - 1) = p + 1 - 2 / p := by
      field_simp; ring
    linarith
  linarith [Real.add_one_le_exp (2 / (p : ℝ))]

theorem prod_ratio_le_exp (S : Finset ℕ) (hS : ∀ p ∈ S, 2 ≤ p) :
    ∏ p ∈ S, (p : ℝ) / ((p : ℝ) - 1) ≤ Real.exp (2 * ∑ p ∈ S, (1 : ℝ) / p) := by
  rw [Finset.mul_sum, Real.exp_sum]
  apply Finset.prod_le_prod
  · intro p hp
    have : (2 : ℝ) ≤ p := by exact_mod_cast hS p hp
    apply div_nonneg <;> linarith
  · intro p hp
    rw [mul_one_div]
    exact ratio_le_exp (hS p hp)

theorem prod_ratio_le_invDelta (z : ℝ) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ (p : ℝ) ≤ z) :
    ∏ p ∈ S, (p : ℝ) / ((p : ℝ) - 1) ≤ 1 / Delta z := by
  have hsub : S ⊆ (Finset.range (⌊z⌋₊ + 1)).filter Nat.Prime := by
    intro p hp
    obtain ⟨hpp, hpz⟩ := hS p hp
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_succ_of_le (Nat.le_floor hpz), hpp⟩
  calc ∏ p ∈ S, (p : ℝ) / ((p : ℝ) - 1)
      ≤ ∏ p ∈ (Finset.range (⌊z⌋₊ + 1)).filter Nat.Prime, (p : ℝ) / ((p : ℝ) - 1) := by
        apply Finset.prod_le_prod_of_subset_of_one_le hsub
        · intro p hp
          have : (2 : ℝ) ≤ p := by exact_mod_cast (hS p hp).1.two_le
          apply div_nonneg <;> linarith
        · intro p hp _
          have : (2 : ℝ) ≤ p := by exact_mod_cast (Finset.mem_filter.1 hp).2.two_le
          rw [le_div_iff₀ (by linarith)]
          linarith
    _ = 1 / Delta z := by
        unfold Delta
        rw [one_div, ← Finset.prod_inv_distrib]
        refine Finset.prod_congr rfl (fun p hp => ?_)
        have : (2 : ℝ) ≤ p := by exact_mod_cast (Finset.mem_filter.1 hp).2.two_le
        rw [one_sub_div (by positivity : (p : ℝ) ≠ 0), inv_div]

/-- Primes of `m ≤ X` above `log X` contribute a bounded factor. -/
theorem prod_bigPrimes_le (X : ℝ) (m : ℕ) (hm : m ≠ 0) (hmX : (m : ℝ) ≤ X)
    (hLX : 1 < Real.log X) (hll : 1 ≤ Real.log (Real.log X)) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p ∈ m.primeFactors ∧ Real.log X < p) :
    ∏ p ∈ S, (p : ℝ) / ((p : ℝ) - 1) ≤ Real.exp 2 := by
  have hprimes : ∀ p ∈ S, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors (hS p hp).1
  have hdiv : ∏ p ∈ S, p ∣ m :=
    Finset.prod_primes_dvd m (fun p hp => (hprimes p hp).prime)
      (fun p hp => Nat.dvd_of_mem_primeFactors (hS p hp).1)
  have hprodle : (∏ p ∈ S, (p : ℝ)) ≤ m := by
    have h1 := Nat.le_of_dvd (Nat.pos_of_ne_zero hm) hdiv
    have h2 : ((∏ p ∈ S, p : ℕ) : ℝ) ≤ m := by exact_mod_cast h1
    rwa [Nat.cast_prod] at h2
  have hpow : (Real.log X) ^ S.card ≤ ∏ p ∈ S, (p : ℝ) := by
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod (fun _ _ => by linarith) (fun p hp => (hS p hp).2.le)
  have hcard : (S.card : ℝ) * Real.log (Real.log X) ≤ Real.log X := by
    have hLpos : 0 < Real.log X := by linarith
    have h1 := Real.log_le_log (pow_pos hLpos _) (hpow.trans (hprodle.trans hmX))
    rw [Real.log_pow] at h1
    exact h1
  have hsum : ∑ p ∈ S, (1 : ℝ) / p ≤ 1 := by
    calc ∑ p ∈ S, (1 : ℝ) / p ≤ ∑ _p ∈ S, (1 : ℝ) / Real.log X :=
          Finset.sum_le_sum (fun p hp => one_div_le_one_div_of_le (by linarith) (hS p hp).2.le)
      _ = S.card / Real.log X := by rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ 1 := by
          rw [div_le_one (by linarith)]
          have : (S.card : ℝ) ≤ (S.card : ℝ) * Real.log (Real.log X) := by
            have h0 : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
            nlinarith
          linarith
  calc ∏ p ∈ S, (p : ℝ) / ((p : ℝ) - 1) ≤ Real.exp (2 * ∑ p ∈ S, (1 : ℝ) / p) :=
        prod_ratio_le_exp S (fun p hp => (hprimes p hp).two_le)
    _ ≤ Real.exp 2 := Real.exp_le_exp.2 (by linarith)

/-- Primes of `σ(n)` above `(log log X)²` contribute a bounded factor (`eq:sv-LP25`). -/
theorem prod_sigmaPrimes_le (X : ℝ) (n : ℕ) (hLP : Eq_SvLP25 X n) (S : Finset ℕ)
    (hS : S ⊆ (sig n).primeFactors.filter (fun r : ℕ => (logIt 2 X) ^ 2 < (r : ℝ))) :
    ∏ p ∈ S, (p : ℝ) / ((p : ℝ) - 1) ≤ Real.exp 2 := by
  have hT2 : ∀ p ∈ (sig n).primeFactors.filter (fun r : ℕ => (logIt 2 X) ^ 2 < (r : ℝ)), 2 ≤ p :=
    fun p hp => (Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hp).1).two_le
  calc ∏ p ∈ S, (p : ℝ) / ((p : ℝ) - 1)
      ≤ ∏ p ∈ (sig n).primeFactors.filter (fun r : ℕ => (logIt 2 X) ^ 2 < (r : ℝ)),
          (p : ℝ) / ((p : ℝ) - 1) := by
        apply Finset.prod_le_prod_of_subset_of_one_le hS
        · intro p hp
          have : (2 : ℝ) ≤ p := by exact_mod_cast hT2 p (hS hp)
          apply div_nonneg <;> linarith
        · intro p hp _
          have : (2 : ℝ) ≤ p := by exact_mod_cast hT2 p hp
          rw [le_div_iff₀ (by linarith)]
          linarith
    _ ≤ Real.exp (2 * ∑ p ∈ (sig n).primeFactors.filter (fun r : ℕ => (logIt 2 X) ^ 2 < (r : ℝ)),
          (1 : ℝ) / p) := prod_ratio_le_exp _ hT2
    _ ≤ Real.exp 2 := by
        apply Real.exp_le_exp.2
        have := hLP
        unfold Eq_SvLP25 at this
        linarith

/-- `log log log X ≤ 4 log Y` for `log log X ≥ 240`. -/
theorem logIt3_le_logY {X : ℝ} (hX1 : 1 < X) (h : 240 ≤ Real.log (Real.log X)) :
    logIt 3 X ≤ 4 * Real.log (SV.Ycut X) := by
  have hX0 : 0 < X := by linarith
  have hL1 : 0 < Real.log X := Real.log_pos hX1
  set L2 := Real.log (Real.log X) with hL2
  have hlu : Real.log (X ^ ((1 : ℝ) / 120)) = Real.log X / 120 := by
    rw [Real.log_rpow hX0]; ring
  set a := Real.log (Real.log (X ^ ((1 : ℝ) / 120))) with ha_def
  have ha : a = L2 - Real.log 120 := by
    rw [ha_def, hlu, Real.log_div hL1.ne' (by norm_num)]
  have hl120 : Real.log 120 ≤ 119 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 120); linarith
  have ha2 : L2 / 2 ≤ a := by rw [ha]; linarith
  have ha0 : 0 < a := by linarith
  have hlog2 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have hL2pos : 0 < L2 := by linarith
  -- `log a ≥ log L2 − 1`
  have hloga : Real.log L2 - 1 ≤ Real.log a := by
    have h1 : Real.log (L2 / 2) ≤ Real.log a := Real.log_le_log (by positivity) ha2
    rw [Real.log_div hL2pos.ne' (by norm_num)] at h1
    linarith
  -- `log L2 ≥ 2`
  have hlogL2 : 2 ≤ Real.log L2 := by
    have he2 : Real.exp 2 ≤ 240 := by
      have h1 := Real.exp_one_lt_d9
      have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      rw [this]; nlinarith [Real.exp_pos 1]
    calc (2 : ℝ) = Real.log (Real.exp 2) := (Real.log_exp 2).symm
      _ ≤ Real.log L2 := Real.log_le_log (Real.exp_pos 2) (by linarith)
  have hloga0 : 0 < Real.log a := by linarith
  have hY : SV.Ycut X = a / Real.log a := by
    unfold SV.Ycut SV.yOf
    rw [logIt_two, logIt_three]
  have hlY : Real.log a / 2 ≤ Real.log (SV.Ycut X) := by
    rw [hY, Real.log_div ha0.ne' hloga0.ne']
    have h1 := log_le_div_e hloga0
    have he : 2 ≤ Real.exp 1 := by have := Real.add_one_le_exp 1; linarith
    have h2 : Real.log a / Real.exp 1 ≤ Real.log a / 2 :=
      div_le_div_of_nonneg_left hloga0.le (by norm_num) he
    linarith
  rw [logIt_three]
  change Real.log L2 ≤ 4 * Real.log (SV.Ycut X)
  linarith


theorem le_mul3 {f a b c : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (h : f ≤ a ∨ f ≤ b ∨ f ≤ c) : f ≤ a * b * c := by
  have hab : 1 ≤ a * b := one_le_mul_of_one_le_of_one_le ha hb
  have h1 : a ≤ a * b * c := by
    calc a = a * 1 * 1 := by ring
      _ ≤ a * b * c := mul_le_mul (mul_le_mul_of_nonneg_left hb (by linarith)) hc
          zero_le_one (by nlinarith)
  have h2 : b ≤ a * b * c := by
    calc b = 1 * b * 1 := by ring
      _ ≤ a * b * c := mul_le_mul (mul_le_mul_of_nonneg_right ha (by linarith)) hc
          zero_le_one (by nlinarith)
  have h3 : c ≤ a * b * c := by
    calc c = 1 * c := by ring
      _ ≤ a * b * c := mul_le_mul_of_nonneg_right hab (by linarith)
  rcases h with h | h | h <;> linarith

open Classical in
/-- `m/φ(m)` splits as the `A'_{3,2}` product (primes in `(z, L]` not dividing `σ`) times the
three remaining products: primes `≤ z`, primes of `σ` above `z`, and primes above `L`. -/
theorem phiRatio_split (m : ℕ) (hm : m ≠ 0) (z L : ℝ) (sg : ℕ) (hsg : sg ≠ 0) :
    ∃ SA SC SE : Finset ℕ, (∀ p ∈ SA, p.Prime ∧ (p : ℝ) ≤ z) ∧
      SC ⊆ sg.primeFactors.filter (fun r : ℕ => z < (r : ℝ)) ∧
      (∀ p ∈ SE, p ∈ m.primeFactors ∧ L < (p : ℝ)) ∧
      SV.phiRatio m ≤ (∏ p ∈ m.primeFactors.filter
          (fun p : ℕ => z < (p : ℝ) ∧ (p : ℝ) ≤ L ∧ ¬ p ∣ sg), (p : ℝ) / ((p : ℝ) - 1)) *
        ((∏ p ∈ SA, (p : ℝ) / ((p : ℝ) - 1)) * (∏ p ∈ SC, (p : ℝ) / ((p : ℝ) - 1)) *
          (∏ p ∈ SE, (p : ℝ) / ((p : ℝ) - 1))) := by
  set S := m.primeFactors.filter (fun p : ℕ => ¬ (z < (p : ℝ) ∧ (p : ℝ) ≤ L ∧ ¬ p ∣ sg)) with hS
  have hSmem : ∀ p ∈ S, p ∈ m.primeFactors ∧ ¬ (z < (p : ℝ) ∧ (p : ℝ) ≤ L ∧ ¬ p ∣ sg) := by
    intro p hp
    rw [hS] at hp
    exact Finset.mem_filter.1 hp
  have hsplit : SV.phiRatio m = (∏ p ∈ m.primeFactors.filter
      (fun p : ℕ => z < (p : ℝ) ∧ (p : ℝ) ≤ L ∧ ¬ p ∣ sg), (p : ℝ) / ((p : ℝ) - 1)) *
      ∏ p ∈ S, (p : ℝ) / ((p : ℝ) - 1) := by
    rw [phiRatio_eq_prod hm, hS, Finset.prod_filter_mul_prod_filter_not]
  clear_value S
  have hSp : ∀ p ∈ S, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors (hSmem p hp).1
  have hf1 : ∀ p ∈ S, 1 ≤ (p : ℝ) / ((p : ℝ) - 1) := by
    intro p hp
    have : (2 : ℝ) ≤ p := by exact_mod_cast (hSp p hp).two_le
    rw [le_div_iff₀ (by linarith)]; linarith
  refine ⟨S.filter (fun p : ℕ => (p : ℝ) ≤ z), S.filter (fun p : ℕ => p ∣ sg ∧ z < (p : ℝ)),
    S.filter (fun p : ℕ => L < (p : ℝ)), ?_, ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨hpS, hpz⟩ := Finset.mem_filter.1 hp
    exact ⟨hSp p hpS, hpz⟩
  · intro p hp
    obtain ⟨hpS, hpd, hzp⟩ := Finset.mem_filter.1 hp
    exact Finset.mem_filter.2 ⟨Nat.mem_primeFactors.2 ⟨hSp p hpS, hpd, hsg⟩, hzp⟩
  · intro p hp
    obtain ⟨hpS, hpL⟩ := Finset.mem_filter.1 hp
    exact ⟨(hSmem p hpS).1, hpL⟩
  · rw [hsplit]
    apply mul_le_mul_of_nonneg_left _ (prod_ratio_nonneg _ (fun p hp =>
      (Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hp).1).one_lt.le))
    rw [Finset.prod_filter, Finset.prod_filter, Finset.prod_filter, ← Finset.prod_mul_distrib,
      ← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod
    · intro p hp
      exact le_trans zero_le_one (hf1 p hp)
    · intro p hp
      have h1 := hf1 p hp
      have hnB := (hSmem p hp).2
      have gA : 1 ≤ (if (p : ℝ) ≤ z then (p : ℝ) / ((p : ℝ) - 1) else 1) := by
        split_ifs <;> linarith
      have gC : 1 ≤ (if p ∣ sg ∧ z < (p : ℝ) then (p : ℝ) / ((p : ℝ) - 1) else 1) := by
        split_ifs <;> linarith
      have gE : 1 ≤ (if L < (p : ℝ) then (p : ℝ) / ((p : ℝ) - 1) else 1) := by
        split_ifs <;> linarith
      apply le_mul3 gA gC gE
      by_cases hA : (p : ℝ) ≤ z
      · left; rw [if_pos hA]
      · have hzp : z < (p : ℝ) := not_le.mp hA
        by_cases hE : L < (p : ℝ)
        · right; right; rw [if_pos hE]
        · have hpd : p ∣ sg := by
            by_contra hnd
            exact hnB ⟨hzp, not_lt.mp hE, hnd⟩
          right; left; rw [if_pos ⟨hpd, hzp⟩]

/-- `A_3 ≤ X` for large `X` (from `A_3 ≤ σ(n) + σ(n') ≤ 2(C_δ+1)X^{7/15}`). -/
theorem A3_le_X {X Cδ : ℝ} {n n' : ℕ} (hX1 : 1 < X) (hXC : (2 * Cδ + 2) ^ 15 ≤ X) (hCδ : 0 < Cδ)
    (hσn : (sig n : ℝ) ≤ (Cδ + 1) * X ^ ((7 : ℝ) / 15))
    (hσn' : (sig n' : ℝ) ≤ (Cδ + 1) * X ^ ((7 : ℝ) / 15)) : (SV.A3 n n' : ℝ) ≤ X := by
  have hX0 : 0 < X := by linarith
  have h1 : SV.A3 n n' ≤ sig n + sig n' := by
    unfold SV.A3
    refine le_trans (Nat.div_le_self _ _) ?_
    have := Int.natAbs_sub_le (sig n : ℤ) (sig n' : ℤ)
    simpa using this
  have h1' : (SV.A3 n n' : ℝ) ≤ sig n + sig n' := by exact_mod_cast h1
  have hX15 : 2 * Cδ + 2 ≤ X ^ ((1 : ℝ) / 15) := by
    have := le_rpow_inv (n := 15) (by norm_num) (by linarith) hXC
    simpa using this
  have hXeq : X = X ^ ((1 : ℝ) / 15) * X ^ ((7 : ℝ) / 15) * X ^ ((7 : ℝ) / 15) := by
    rw [rpow_mul_rpow hX0, rpow_mul_rpow hX0]; norm_num
  have h7 : 0 < X ^ ((7 : ℝ) / 15) := Real.rpow_pos_of_pos hX0 _
  have h7' : 1 ≤ X ^ ((7 : ℝ) / 15) := Real.one_le_rpow hX1.le (by norm_num)
  have : 2 * (Cδ + 1) * X ^ ((7 : ℝ) / 15) ≤ X := by
    calc 2 * (Cδ + 1) * X ^ ((7 : ℝ) / 15) = (2 * Cδ + 2) * X ^ ((7 : ℝ) / 15) := by ring
      _ ≤ X ^ ((1 : ℝ) / 15) * X ^ ((7 : ℝ) / 15) := mul_le_mul_of_nonneg_right hX15 h7.le
      _ ≤ X ^ ((1 : ℝ) / 15) * X ^ ((7 : ℝ) / 15) * X ^ ((7 : ℝ) / 15) :=
          le_mul_of_one_le_right (by positivity) h7'
      _ = X := hXeq.symm
  linarith

/-- Mertens at `z = (log log X)²`: `1/Δ(z) ≤ 16 e^γ log Y`, and `log Y > 0`. -/
theorem invDelta_bound {X y₀ : ℝ}
    (hy₀ : ∀ b ≥ y₀, Real.exp (-eulerGamma) / 2 < Delta b * Real.log b) (hX1 : 1 < X)
    (hll : max y₀ 240 ≤ Real.log (Real.log X)) :
    1 / Delta ((logIt 2 X) ^ 2) ≤ 16 * Real.exp eulerGamma * Real.log (SV.Ycut X) ∧
      0 < Real.log (SV.Ycut X) := by
  have hll240 : 240 ≤ Real.log (Real.log X) := le_trans (le_max_right _ _) hll
  set z := (logIt 2 X) ^ 2 with hz
  have hz2 : logIt 2 X = Real.log (Real.log X) := logIt_two X
  have hzy : y₀ ≤ z := by
    rw [hz, hz2]
    have h1 : y₀ ≤ Real.log (Real.log X) := le_trans (le_max_left _ _) hll
    nlinarith
  have hMz := hy₀ z hzy
  have hlogz : Real.log z = 2 * logIt 3 X := by
    rw [hz, Real.log_pow, logIt_three, hz2]; push_cast; ring
  have hl3 : 0 < logIt 3 X := by
    rw [logIt_three]; exact Real.log_pos (by linarith)
  have hlogz0 : 0 < Real.log z := by rw [hlogz]; linarith
  have hΔ : 1 / Delta z ≤ 2 * Real.exp eulerGamma * Real.log z := by
    have hpos : 0 < Real.exp (-eulerGamma) / 2 := by positivity
    have hΔ0 : 0 < Delta z := by
      by_contra hle
      have : Delta z * Real.log z ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hle) hlogz0.le
      linarith
    rw [div_le_iff₀ hΔ0]
    have e : Real.exp eulerGamma * Real.exp (-eulerGamma) = 1 := by
      rw [← Real.exp_add]; simp
    have hg := Real.exp_pos eulerGamma
    have : 2 * Real.exp eulerGamma * (Real.exp (-eulerGamma) / 2) = 1 := by linarith
    calc (1 : ℝ) = 2 * Real.exp eulerGamma * (Real.exp (-eulerGamma) / 2) := this.symm
      _ ≤ 2 * Real.exp eulerGamma * (Delta z * Real.log z) :=
          mul_le_mul_of_nonneg_left hMz.le (by positivity)
      _ = 2 * Real.exp eulerGamma * Real.log z * Delta z := by ring
  have hlogY := logIt3_le_logY hX1 hll240
  refine ⟨?_, by linarith⟩
  rw [hlogz] at hΔ
  have hg := Real.exp_pos eulerGamma
  calc 1 / Delta z ≤ 2 * Real.exp eulerGamma * (2 * logIt 3 X) := hΔ
    _ = 4 * Real.exp eulerGamma * logIt 3 X := by ring
    _ ≤ 4 * Real.exp eulerGamma * (4 * Real.log (SV.Ycut X)) :=
        mul_le_mul_of_nonneg_left hlogY (by positivity)
    _ = 16 * Real.exp eulerGamma * Real.log (SV.Ycut X) := by ring

theorem link_A3Reduction : Spine.Link_Claim_SvA3Reduction := by
  intro hTS hM3
  refine ⟨16 * Real.exp eulerGamma * (Real.exp 2 * Real.exp 2), ?_⟩
  intro δ hδ hδ1 D hD 𝒜 hreg
  obtain ⟨Cδ, hCδ, X₃, hX₃⟩ := hTS δ hδ hδ1 D hD
  obtain ⟨c0, _, B, _, X₀, hX₀⟩ := hreg
  have hev := (tendsto_order.1 hM3).1 (Real.exp (-eulerGamma) / 2)
    (half_lt_self (Real.exp_pos _))
  obtain ⟨y₀, hy₀⟩ := Filter.eventually_atTop.1 hev
  refine ⟨max (max X₀ X₃) (max (Real.exp (Real.exp (max y₀ 240))) ((2 * Cδ + 2) ^ 15)), ?_⟩
  intro X hX d n n' hpair
  have hXa : X₀ ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hXb : X₃ ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hXe : Real.exp (Real.exp (max y₀ 240)) ≤ X :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hX
  have hXC : (2 * Cδ + 2) ^ 15 ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hX
  have hX0 : 0 < X := lt_of_lt_of_le (Real.exp_pos _) hXe
  have hlX : Real.exp (max y₀ 240) ≤ Real.log X := by
    calc Real.exp (max y₀ 240) = Real.log (Real.exp (Real.exp (max y₀ 240))) :=
          (Real.log_exp _).symm
      _ ≤ Real.log X := Real.log_le_log (Real.exp_pos _) hXe
  have hllX : max y₀ 240 ≤ Real.log (Real.log X) := by
    calc max y₀ 240 = Real.log (Real.exp (max y₀ 240)) := (Real.log_exp _).symm
      _ ≤ Real.log (Real.log X) := Real.log_le_log (Real.exp_pos _) hlX
  have hll240 : 240 ≤ Real.log (Real.log X) := le_trans (le_max_right _ _) hllX
  have hLX1 : 1 < Real.log X := by
    have h1 : (240 : ℝ) + 1 ≤ Real.exp (max y₀ 240) := by
      have := Real.add_one_le_exp (max y₀ 240)
      have : (240 : ℝ) ≤ max y₀ 240 := le_max_right _ _
      linarith
    linarith
  have hX1 : 1 < X := by
    by_contra hle
    have : Real.log X ≤ 0 := Real.log_nonpos hX0.le (not_lt.mp hle)
    linarith
  have hA := (hX₀ X hXa).2.2
  obtain ⟨_hne, p₀, p₀', hN0, hN0', _hcoll0⟩ := hpair
  obtain ⟨q, r, k, ht, hn⟩ := hN0
  have hLP : Eq_SvLP25 X n := by rw [hn]; exact (member_reg hA ht).2.2.2.2.2.1
  have hσbound : ∀ p m : ℕ, SV.IsNPart D (𝒜 X) X d p m →
      (sig m : ℝ) ≤ (Cδ + 1) * X ^ ((7 : ℝ) / 15) := by
    intro p m hm
    obtain ⟨q, r, k, ht, rfl⟩ := hm
    have hT := ht.1
    have hpos := tuple_n_pos hX1.le hT
    have h := hX₃ X hXb p q r k hT (q * r * k) (Or.inr (Or.inr (Or.inl rfl)))
    have h1 := aliquot_lt_of_ratio hpos h.2
    have h2 := tuple_n_le hX1.le hT
    have e : (sig (q * r * k) : ℝ) = aliquot (q * r * k) + ((q * r * k : ℕ) : ℝ) := by
      exact_mod_cast sig_eq_aliquot_add (q * r * k)
    rw [e]
    have : (Cδ + 1) * ((q * r * k : ℕ) : ℝ) ≤ (Cδ + 1) * X ^ ((7 : ℝ) / 15) :=
      mul_le_mul_of_nonneg_left h2 (by linarith)
    linarith
  have hA3X := A3_le_X hX1 hXC hCδ (hσbound p₀ n ⟨q, r, k, ht, hn⟩) (hσbound p₀' n' hN0')
  have hn0 : n ≠ 0 := by rw [hn]; exact (tuple_n_pos hX1.le ht.1).ne'
  have hsig0 : sig n ≠ 0 := by have := le_sig n; omega
  obtain ⟨hInv, hlogY0⟩ := invDelta_bound hy₀ hX1 hllX
  have h32nn : 0 ≤ SV.ratio32 X n n' := ratio32_nonneg X n n'
  rcases Nat.eq_zero_or_pos (SV.A3 n n') with hA30 | hA3pos
  · rw [hA30]
    have : SV.phiRatio 0 = 0 := by unfold SV.phiRatio; simp
    rw [this]
    positivity
  obtain ⟨SA, SC, SE, hSA, hSC, hSE, hsplit⟩ :=
    phiRatio_split (SV.A3 n n') hA3pos.ne' ((logIt 2 X) ^ 2) (Real.log X) (sig n) hsig0
  have hPA := (prod_ratio_le_invDelta _ SA hSA).trans hInv
  have hPC := prod_sigmaPrimes_le X n hLP SC hSC
  have hPE := prod_bigPrimes_le X (SV.A3 n n') hA3pos.ne' hA3X hLX1 (by linarith) SE hSE
  have hPA0 : 0 ≤ ∏ p ∈ SA, (p : ℝ) / ((p : ℝ) - 1) :=
    prod_ratio_nonneg _ (fun p hp => (hSA p hp).1.one_lt.le)
  have hPC0 : 0 ≤ ∏ p ∈ SC, (p : ℝ) / ((p : ℝ) - 1) :=
    prod_ratio_nonneg _ (fun p hp =>
      (Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 (hSC hp)).1).one_lt.le)
  have hPE0 : 0 ≤ ∏ p ∈ SE, (p : ℝ) / ((p : ℝ) - 1) :=
    prod_ratio_nonneg _ (fun p hp => (Nat.prime_of_mem_primeFactors (hSE p hp).1).one_lt.le)
  have hrest : (∏ p ∈ SA, (p : ℝ) / ((p : ℝ) - 1)) * (∏ p ∈ SC, (p : ℝ) / ((p : ℝ) - 1)) *
      (∏ p ∈ SE, (p : ℝ) / ((p : ℝ) - 1)) ≤
      16 * Real.exp eulerGamma * Real.log (SV.Ycut X) * Real.exp 2 * Real.exp 2 := by
    have h1 := mul_le_mul hPA hPC hPC0 (by positivity)
    exact mul_le_mul h1 hPE hPE0 (by positivity)
  have h32 : ∏ p ∈ (SV.A3 n n').primeFactors.filter (fun p : ℕ => (logIt 2 X) ^ 2 < (p : ℝ) ∧
      (p : ℝ) ≤ Real.log X ∧ ¬ p ∣ sig n), (p : ℝ) / ((p : ℝ) - 1) = SV.ratio32 X n n' := by
    unfold SV.ratio32; rfl
  rw [h32] at hsplit
  calc SV.phiRatio (SV.A3 n n')
      ≤ SV.ratio32 X n n' * ((∏ p ∈ SA, (p : ℝ) / ((p : ℝ) - 1)) *
          (∏ p ∈ SC, (p : ℝ) / ((p : ℝ) - 1)) * (∏ p ∈ SE, (p : ℝ) / ((p : ℝ) - 1))) := hsplit
    _ ≤ SV.ratio32 X n n' * (16 * Real.exp eulerGamma * Real.log (SV.Ycut X) * Real.exp 2 *
          Real.exp 2) := mul_le_mul_of_nonneg_left hrest h32nn
    _ = 16 * Real.exp eulerGamma * (Real.exp 2 * Real.exp 2) * Real.log (SV.Ycut X) *
          SV.ratio32 X n n' := by ring

end Principia.Erdos1054.Proofs.SvLargeH

namespace Principia.Erdos1054.Proofs

/-- `eq:sv-collision` (leaf), EP1054.tex lines 1562–1566: `s(pn) = p s(n) + σ(n)` for a prime
`p ∤ n`. -/
theorem leaf_Eq_SvCollision : Principia.Erdos1054.Eq_SvCollision :=
  SvLargeH.collision

/-- `eq:sv-totient`, EP1054.tex lines 1620–1627. -/
theorem link_Eq_SvTotient : Principia.Erdos1054.Spine.Link_Eq_SvTotient :=
  SvLargeH.totient_link

/-- Off-diagonal nondegeneracy `σ(n) ≠ σ(n')`, EP1054.tex lines 1572–1580. -/
theorem link_Claim_SvSigmaDistinct : Principia.Erdos1054.Spine.Link_Claim_SvSigmaDistinct :=
  SvLargeH.link_sigmaDistinct

/-- The unit claim of the large-`h` case, EP1054.tex lines 1663–1676. -/
theorem link_Claim_SvLargeHUnits : Principia.Erdos1054.Spine.Link_Claim_SvLargeHUnits :=
  SvLargeH.link_units

/-- `eq:sv-large-h-congruence`, EP1054.tex lines 1677–1684. -/
theorem link_Eq_SvLargeHCongruence : Principia.Erdos1054.Spine.Link_Eq_SvLargeHCongruence :=
  SvLargeH.link_congruence

/-- The large-`h` rigidity `ℓ = ℓ'`, `q ≡ q' (mod h)`, EP1054.tex lines 1663–1708. -/
theorem link_Claim_SvLargeHRigidity : Principia.Erdos1054.Spine.Link_Claim_SvLargeHRigidity :=
  SvLargeH.link_rigidity

/-- The large-`h` contribution, EP1054.tex lines 1710–1731. -/
theorem link_Claim_SvLargeH : Principia.Erdos1054.Spine.Link_Claim_SvLargeH :=
  SvLargeH.link_largeH

/-- The reduction `A'_{3,2} → A''_{3,2}`, EP1054.tex lines 1733–1739. -/
theorem link_Claim_SvA322Reduction : Principia.Erdos1054.Spine.Link_Claim_SvA322Reduction :=
  SvLargeH.link_A322

/-- `eq:sv-reduced-collision-sum`, EP1054.tex lines 1647–1657 (large-`h` plus small-`h`). -/
theorem link_Eq_SvReducedCollisionSum :
    Principia.Erdos1054.Spine.Link_Eq_SvReducedCollisionSum :=
  SvLargeH.link_reducedSum

/-- The sieve bound for a fixed collision pair, EP1054.tex lines 1588–1618. -/
theorem link_Claim_SvSievePairs : Principia.Erdos1054.Spine.Link_Claim_SvSievePairs :=
  SvLargeH.link_sievePairs

/-- The reduction of the `A_3` factor, EP1054.tex lines 1631–1646. -/
theorem link_Claim_SvA3Reduction : Principia.Erdos1054.Spine.Link_Claim_SvA3Reduction :=
  SvLargeH.link_A3Reduction

end Principia.Erdos1054.Proofs
