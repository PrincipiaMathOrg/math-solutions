/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.PSieveBasic
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.Harmonic.Bounds

set_option autoImplicit false

/-!
# Comparisons of `G_q(R) = ∑_{r ≤ R, (r,q)=1} μ²(r)/φ(r)` (Helfgott `ternvin.tex` 2642-2656,
2773-2784)

The elementary inequalities of `subs:boquo` that `lem:trivo` and `prop:espagn`'s reduction use
(C7 of the `CoeurY` spine):

* `gQ_mono` — `G_q` is non-decreasing (`eq:triwia`, 3402-3405, is `gQ_mono` at `s`-scaled
  arguments);
* `gQ_mul_le` — `lem:trivo`'s `eq:bete` (2773-2777): `G_q(A)·G_𝒫(B) ≤ G_q(AB)` when `𝒫` is
  divisible by every prime `≤ A` and every prime dividing `q`;
* `gQ_one_le_wq`, `wq_mul_le` — `eq:hosmo` (2650-2656): `G(R) ≤ (q/φ(q))G_q(R) ≤ G(Rq)`, with
  `q/φ(q) = ∑_{d ∣ q} μ²(d)/φ(d)` (`wq_eq`, by multiplicativity), obtained, as the source says,
  "by multiplying term-by-term by `q/φ(q)`": every squarefree `m` is `d·r` with `d ∣ q`,
  `(r, q) = 1`, uniquely;
* `trivo_mogan` — `lem:trivo`'s first inequality `G_q(A)/G_q(AB) ≤ (𝒫/φ(𝒫))/G(B)` (`eq:mogan`);
  the rest of `lem:trivo` is `lem:suspiro` (Rosser–Schoenfeld 1962 (3.42), 1975 (5.1), and a
  computation) and `eq:charpy` (a machine check), neither formalized here;
* `sum_inv_le_gQ`, `log_lt_gQ` — `eq:coro` (2643-2649): `G(R) ≥ ∑_{r ≤ R} 1/r > log R`, from the
  fibers of the radical and Euler's product over `P`-factored numbers (`sum_inv_le_prod`).
-/

namespace Principia.Common.PSieve

open ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

/-- The summand `μ²(m)/φ(m)`. -/
noncomputable def gt (m : ℕ) : ℝ := ((μ m : ℤ) : ℝ) ^ 2 / (m.totient : ℝ)

/-- The index set of `G_q(R)`. -/
noncomputable def sq (q : ℕ) (R : ℝ) : Finset ℕ :=
  (Finset.Icc 1 ⌊R⌋₊).filter (fun r => Nat.Coprime r q)

/-- `G_q(R) = ∑_{r ∈ sq q R} μ²(r)/φ(r)`, by `rfl`. -/
theorem gQ_eq_gt (q : ℕ) (R : ℝ) : gQ q R = ∑ r ∈ sq q R, gt r := rfl

/-- `μ²(m)/φ(m) ≥ 0`. -/
theorem gt_nonneg (m : ℕ) : 0 ≤ gt m := div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)

/-- `μ²/φ` is multiplicative. -/
theorem gt_mul {a b : ℕ} (h : Nat.Coprime a b) : gt (a * b) = gt a * gt b := by
  unfold gt
  rw [isMultiplicative_moebius.map_mul_of_coprime h, Nat.totient_mul h]
  push_cast
  rw [mul_pow, mul_div_mul_comm]

/-- **`G_q` is non-decreasing** (the trivial bound `eq:triwia`). -/
theorem gQ_mono (q : ℕ) {R R' : ℝ} (h : R ≤ R') : gQ q R ≤ gQ q R' := by
  rw [gQ_eq_gt, gQ_eq_gt]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun m _ _ => gt_nonneg m
  intro m hm
  simp only [sq, Finset.mem_filter, Finset.mem_Icc] at hm ⊢
  exact ⟨⟨hm.1.1, le_trans hm.1.2 (Nat.floor_le_floor h)⟩, hm.2⟩

/-- Membership in `sq`, as real inequalities. -/
theorem mem_sq {q : ℕ} {R : ℝ} {r : ℕ} (h : r ∈ sq q R) :
    1 ≤ r ∧ (r : ℝ) ≤ R ∧ Nat.Coprime r q := by
  simp only [sq, Finset.mem_filter, Finset.mem_Icc] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have hpos : 0 < ⌊R⌋₊ := by omega
  have hR : 0 ≤ R := le_trans zero_le_one (Nat.floor_pos.mp hpos)
  exact ⟨h1, le_trans (by exact_mod_cast h2) (Nat.floor_le hR), h3⟩

/-- Building a member of `sq`. -/
theorem sq_mem {q : ℕ} {R : ℝ} {r : ℕ} (h1 : 1 ≤ r) (h2 : (r : ℝ) ≤ R)
    (h3 : Nat.Coprime r q) : r ∈ sq q R := by
  simp only [sq, Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨h1, Nat.le_floor h2⟩, h3⟩

/-! ## `lem:trivo`'s `eq:bete` -/

/-- **`eq:bete`** (`ternvin.tex` 2773-2777): if `𝒫` is divisible by every prime `≤ A` and by every
prime dividing `q`, then `G_q(A)·G_𝒫(B) ≤ G_q(AB)` — `(r, r') ↦ rr'` is injective on
`r ≤ A`, `(r', 𝒫) = 1`, lands in `rr' ≤ AB`, `(rr', q) = 1`, and `μ²/φ` is multiplicative. -/
theorem gQ_mul_le (q P : ℕ) (A B : ℝ) (hA : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ A → p ∣ P)
    (hq : ∀ p : ℕ, p.Prime → p ∣ q → p ∣ P) : gQ q A * gQ P B ≤ gQ q (A * B) := by
  classical
  rw [gQ_eq_gt, gQ_eq_gt, gQ_eq_gt, Finset.sum_mul_sum, ← Finset.sum_product']
  -- the two factors are coprime
  have hcop : ∀ x ∈ sq q A ×ˢ sq P B, Nat.Coprime x.1 x.2 := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := Finset.mem_product.mp hx
    obtain ⟨h1, h2, -⟩ := mem_sq hx1
    obtain ⟨-, -, h6⟩ := mem_sq hx2
    refine Nat.coprime_of_dvd fun p hp hp1 hp2 => ?_
    have hpA : (p : ℝ) ≤ A := le_trans (by exact_mod_cast Nat.le_of_dvd (by omega) hp1) h2
    have hpP := hA p hp hpA
    exact hp.one_lt.ne' ((h6.coprime_dvd_left hp2).eq_one_of_dvd hpP)
  have e1 : ∀ x ∈ sq q A ×ˢ sq P B, gt x.1 * gt x.2 = gt (x.1 * x.2) := fun x hx =>
    (gt_mul (hcop x hx)).symm
  rw [Finset.sum_congr rfl e1]
  have hinj : Set.InjOn (fun x : ℕ × ℕ => x.1 * x.2) ↑(sq q A ×ˢ sq P B) := by
    rintro ⟨r₁, s₁⟩ h₁ ⟨r₂, s₂⟩ h₂ he
    simp only at he
    have hc1 := hcop _ h₁
    have hc2 := hcop _ h₂
    have hr1 : r₁ ∈ sq q A := (Finset.mem_product.mp (Finset.mem_coe.mp h₁)).1
    have hs1 : s₁ ∈ sq P B := (Finset.mem_product.mp (Finset.mem_coe.mp h₁)).2
    have hr2 : r₂ ∈ sq q A := (Finset.mem_product.mp (Finset.mem_coe.mp h₂)).1
    have hs2 : s₂ ∈ sq P B := (Finset.mem_product.mp (Finset.mem_coe.mp h₂)).2
    -- `r₁` is coprime to `s₂` (its primes are `≤ A`, those of `s₂` avoid `𝒫`)
    have cross : ∀ {r s : ℕ}, r ∈ sq q A → s ∈ sq P B → Nat.Coprime r s := fun {r s} hr hs =>
      hcop (r, s) (Finset.mem_product.mpr ⟨hr, hs⟩)
    have d1 : r₁ ∣ r₂ := (cross hr1 hs2).dvd_of_dvd_mul_right ⟨s₁, by rw [he]⟩
    have d2 : r₂ ∣ r₁ := (cross hr2 hs1).dvd_of_dvd_mul_right ⟨s₂, by rw [he]⟩
    have hr : r₁ = r₂ := Nat.dvd_antisymm d1 d2
    subst hr
    have hpos : 0 < r₁ := (mem_sq hr1).1
    have hs : s₁ = s₂ := Nat.eq_of_mul_eq_mul_left hpos he
    rw [hs]
  rw [← Finset.sum_image hinj]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun m _ _ => gt_nonneg m
  intro m hm
  obtain ⟨⟨r, s⟩, hx, rfl⟩ := Finset.mem_image.mp hm
  obtain ⟨hr, hs⟩ := Finset.mem_product.mp hx
  obtain ⟨h1, h2, h3⟩ := mem_sq hr
  obtain ⟨h4, h5, h6⟩ := mem_sq hs
  refine sq_mem (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))) ?_ ?_
  · push_cast
    exact mul_le_mul h2 h5 (Nat.cast_nonneg _) (le_trans (Nat.cast_nonneg _) h2)
  · refine Nat.coprime_mul_iff_left.mpr ⟨h3, Nat.coprime_of_dvd fun p hp hp1 hp2 => ?_⟩
    exact hp.one_lt.ne' ((h6.coprime_dvd_left hp1).eq_one_of_dvd (hq p hp hp2))

/-! ## `eq:hosmo` -/

/-- **`w(q) = ∑_{d ∣ q} μ²(d)/φ(d)`** (`= q/φ(q)`, `wq_eq`). -/
noncomputable def wq (q : ℕ) : ℝ := ∑ d ∈ q.divisors, gt d

/-- For `d ∣ q` and `(r, q) = 1`: `gcd(dr, q) = d`. -/
theorem gcd_mul_cop {d r q : ℕ} (hd : d ∣ q) (hr : Nat.Coprime r q) : Nat.gcd (d * r) q = d := by
  rw [Nat.Coprime.gcd_mul_right_cancel d hr, Nat.gcd_eq_left hd]

/-- `(d, r) ↦ dr` is injective on `{d ∣ q} × {(r, q) = 1}`. -/
theorem injOn_div (q : ℕ) (R : ℝ) :
    Set.InjOn (fun x : ℕ × ℕ => x.1 * x.2) ↑(q.divisors ×ˢ sq q R) := by
  rintro ⟨d₁, r₁⟩ h₁ ⟨d₂, r₂⟩ h₂ he
  simp only at he
  have hd1 : d₁ ∈ q.divisors := (Finset.mem_product.mp (Finset.mem_coe.mp h₁)).1
  have hr1 : r₁ ∈ sq q R := (Finset.mem_product.mp (Finset.mem_coe.mp h₁)).2
  have hd2 : d₂ ∈ q.divisors := (Finset.mem_product.mp (Finset.mem_coe.mp h₂)).1
  have hr2 : r₂ ∈ sq q R := (Finset.mem_product.mp (Finset.mem_coe.mp h₂)).2
  have g1 := gcd_mul_cop (Nat.dvd_of_mem_divisors hd1) (mem_sq hr1).2.2
  have g2 := gcd_mul_cop (Nat.dvd_of_mem_divisors hd2) (mem_sq hr2).2.2
  have hd : d₁ = d₂ := by rw [← g1, ← g2, he]
  subst hd
  have hpos : 0 < d₁ := Nat.pos_of_mem_divisors hd1
  have hr : r₁ = r₂ := Nat.eq_of_mul_eq_mul_left hpos he
  rw [hr]

/-- `w(q)·G_q(R) = ∑_{d ∣ q} ∑_{(r,q)=1} μ²(dr)/φ(dr)`. -/
theorem wq_mul_eq (q : ℕ) (R : ℝ) :
    wq q * gQ q R = ∑ m ∈ (q.divisors ×ˢ sq q R).image (fun x => x.1 * x.2), gt m := by
  classical
  rw [wq, gQ_eq_gt, Finset.sum_mul_sum, ← Finset.sum_product', Finset.sum_image (injOn_div q R)]
  refine Finset.sum_congr rfl fun x hx => ?_
  obtain ⟨hd, hr⟩ := Finset.mem_product.mp hx
  have hc : Nat.Coprime x.1 x.2 :=
    ((mem_sq hr).2.2.coprime_dvd_right (Nat.dvd_of_mem_divisors hd)).symm
  exact (gt_mul hc).symm

/-- **`eq:hosmo`, left** (`ternvin.tex` 2650-2656): `G(R) ≤ (q/φ(q))·G_q(R)`, i.e.
`G(R) ≤ w(q)G_q(R)` (`q ≥ 1`): every squarefree `m ≤ R` is `gcd(m,q)·(m/gcd(m,q))`. -/
theorem gQ_one_le_wq (q : ℕ) (hq : 1 ≤ q) (R : ℝ) : gQ 1 R ≤ wq q * gQ q R := by
  classical
  rw [wq_mul_eq, gQ_eq_gt, ← Finset.sum_filter_ne_zero]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun m _ _ => gt_nonneg m
  intro m hm
  obtain ⟨hm1, hm0⟩ := Finset.mem_filter.mp hm
  obtain ⟨h1, h2, -⟩ := mem_sq hm1
  have hμ : μ m ≠ 0 := by
    intro h0
    apply hm0
    unfold gt
    rw [h0]
    simp
  have hsf : Squarefree m := by
    by_contra hns
    exact hμ (moebius_eq_zero_of_not_squarefree hns)
  set d := Nat.gcd m q with hd
  have hdq : d ∣ q := Nat.gcd_dvd_right m q
  have hdm : d ∣ m := Nat.gcd_dvd_left m q
  have hd0 : 0 < d := Nat.gcd_pos_of_pos_left q (by omega)
  have hmd : d * (m / d) = m := Nat.mul_div_cancel' hdm
  refine Finset.mem_image.mpr ⟨(d, m / d), Finset.mem_product.mpr ⟨?_, ?_⟩, hmd⟩
  · exact Nat.mem_divisors.mpr ⟨hdq, by omega⟩
  · refine sq_mem (Nat.div_pos (Nat.le_of_dvd (by omega) hdm) hd0) ?_ ?_
    · exact le_trans (by exact_mod_cast Nat.div_le_self m d) h2
    · refine Nat.coprime_of_dvd fun p hp hp1 hp2 => ?_
      -- `p ∣ m/d` and `p ∣ q` put `p²` in `m`
      have hpm : p ∣ m := dvd_trans hp1 (Nat.div_dvd_of_dvd hdm)
      have hpd : p ∣ d := Nat.dvd_gcd hpm hp2
      have hpp : p * p ∣ m := by
        rw [← hmd]
        exact Nat.mul_dvd_mul hpd hp1
      exact hp.one_lt.ne' (Nat.isUnit_iff.mp (hsf p hpp))

/-- **`eq:hosmo`, right**: `(q/φ(q))·G_q(R) ≤ G(Rq)`, i.e. `w(q)G_q(R) ≤ G(qR)`. -/
theorem wq_mul_le (q : ℕ) (R : ℝ) : wq q * gQ q R ≤ gQ 1 (q * R) := by
  classical
  rw [wq_mul_eq, gQ_eq_gt]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun m _ _ => gt_nonneg m
  intro m hm
  obtain ⟨⟨d, r⟩, hx, rfl⟩ := Finset.mem_image.mp hm
  obtain ⟨hd, hr⟩ := Finset.mem_product.mp hx
  obtain ⟨h1, h2, -⟩ := mem_sq hr
  have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
  have hdq : (d : ℝ) ≤ q := by
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (Nat.mem_divisors.mp hd).2)
      (Nat.dvd_of_mem_divisors hd)
  refine sq_mem (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))) ?_
    (Nat.coprime_one_right _)
  push_cast
  exact mul_le_mul hdq h2 (Nat.cast_nonneg _) (le_trans (Nat.cast_nonneg _) hdq)

/-- **`lem:trivo`'s `eq:mogan`, first inequality** (`ternvin.tex` 2773-2798): with `𝒫` as in
`gQ_mul_le` and `B ≥ 1`, `G_q(A) ≤ (w(𝒫)/G(B))·G_q(AB)`, i.e.
`G_q(Q₀/sq)/G_q(Q/sq) ≤ (𝒫/φ(𝒫))/G(Q/Q₀)` at `A = Q₀/sq`, `B = Q/Q₀` (`wq_eq`: `w(𝒫) = 𝒫/φ(𝒫)`).
The rest of `lem:trivo` is `lem:suspiro` (Rosser–Schoenfeld) and `eq:charpy` (a machine check). -/
theorem trivo_mogan (q P : ℕ) (hP1 : 1 ≤ P) (A B : ℝ) (hB : 1 ≤ B)
    (hA : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ A → p ∣ P) (hq : ∀ p : ℕ, p.Prime → p ∣ q → p ∣ P) :
    gQ q A ≤ wq P / gQ 1 B * gQ q (A * B) := by
  have h1 := gQ_mul_le q P A B hA hq
  have h2 := gQ_one_le_wq P hP1 B
  have hG : 0 < gQ 1 B := lt_of_lt_of_le one_pos (one_le_gQ 1 B hB)
  have hqA := gQ_nonneg q A
  rw [div_mul_eq_mul_div, le_div_iff₀ hG]
  calc gQ q A * gQ 1 B ≤ gQ q A * (wq P * gQ P B) := mul_le_mul_of_nonneg_left h2 hqA
    _ = wq P * (gQ q A * gQ P B) := by ring
    _ ≤ wq P * gQ q (A * B) := by
      have hw : 0 ≤ wq P := Finset.sum_nonneg fun d _ => gt_nonneg d
      exact mul_le_mul_of_nonneg_left h1 hw

/-! ## `q/φ(q) = ∑_{d ∣ q} μ²(d)/φ(d)` -/

/-- `μ²/φ` as an arithmetic function. -/
noncomputable def gtF : ArithmeticFunction ℝ := ⟨gt, by simp [gt]⟩

/-- `n/φ(n)` as an arithmetic function. -/
noncomputable def ratF : ArithmeticFunction ℝ := ⟨fun n => (n : ℝ) / n.totient, by simp⟩

/-- `μ²/φ` is multiplicative. -/
theorem gtF_mult : gtF.IsMultiplicative := by
  refine ⟨?_, fun {m n} h => gt_mul h⟩
  change gt 1 = 1
  simp [gt]

/-- `n/φ(n)` is multiplicative. -/
theorem ratF_mult : ratF.IsMultiplicative := by
  refine ⟨?_, fun {m n} h => ?_⟩
  · change ((1 : ℕ) : ℝ) / (Nat.totient 1 : ℝ) = 1
    simp
  · change ((m * n : ℕ) : ℝ) / ((m * n).totient : ℝ) =
      (m : ℝ) / m.totient * ((n : ℝ) / n.totient)
    rw [Nat.totient_mul h]
    push_cast
    rw [mul_div_mul_comm]

/-- **`q/φ(q) = ∑_{d ∣ q} μ²(d)/φ(d)`** (`q ≥ 1`): both sides multiplicative, and on `p^k`,
`k ≥ 1`, both are `1 + 1/(p−1) = p/(p−1)`. -/
theorem wq_eq (q : ℕ) : wq q = q / q.totient := by
  have hmul : (gtF * (ζ : ArithmeticFunction ℝ)).IsMultiplicative :=
    gtF_mult.mul isMultiplicative_zeta.natCast
  have heq : gtF * (ζ : ArithmeticFunction ℝ) = ratF := by
    rw [IsMultiplicative.eq_iff_eq_on_prime_powers _ hmul _ ratF_mult]
    intro p i hp
    rw [coe_mul_zeta_apply, Nat.sum_divisors_prime_pow hp]
    change ∑ x ∈ Finset.range (i + 1), gt (p ^ x) = ((p ^ i : ℕ) : ℝ) / (p ^ i).totient
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp [gt]
    · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      rw [Finset.sum_range_succ', Finset.sum_range_succ']
      have hz : ∀ x ∈ Finset.range j, gt (p ^ (x + 1 + 1)) = 0 := by
        intro x _
        unfold gt
        rw [moebius_apply_prime_pow hp (by omega), if_neg (by omega)]
        simp
      rw [Finset.sum_eq_zero hz, Nat.totient_prime_pow hp (by omega)]
      have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
      have hpc : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
        rw [Nat.cast_sub hp.one_le, Nat.cast_one]
      unfold gt
      rw [zero_add, pow_one, moebius_apply_prime hp, Nat.totient_prime hp, pow_zero,
        moebius_apply_one, Nat.totient_one]
      push_cast
      rw [hpc]
      have hp0 : (p : ℝ) - 1 ≠ 0 := by linarith
      have hpj : (p : ℝ) ^ j ≠ 0 := pow_ne_zero _ (by linarith)
      field_simp
      ring
  have h : (gtF * (ζ : ArithmeticFunction ℝ)) q = ratF q := by rw [heq]
  rw [coe_mul_zeta_apply] at h
  exact h

/-! ## `eq:coro`: `G(R) ≥ ∑_{r ≤ R} 1/r > log R` -/

/-- `m ↦ 1/m`, completely multiplicative. -/
noncomputable def invHom : ℕ →* ℝ where
  toFun m := (m : ℝ)⁻¹
  map_one' := by simp
  map_mul' a b := by
    push_cast
    rw [mul_inv]

/-- **Euler's product over `P`-factored numbers, truncated**: `∑_{k ∈ K} 1/k ≤ ∏_{p ∈ P}
(1 − 1/p)⁻¹` for a finite `K` of positive integers with every prime factor in `P`
(`EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric`). -/
theorem sum_inv_le_prod (P K : Finset ℕ) (hK : ∀ k ∈ K, k ∈ Nat.factoredNumbers P) :
    ∑ k ∈ K, (k : ℝ)⁻¹ ≤ ∏ p ∈ P with p.Prime, (1 - (p : ℝ)⁻¹)⁻¹ := by
  have hn : ∀ {p : ℕ}, p.Prime → ‖invHom p‖ < 1 := by
    intro p hp
    change ‖(p : ℝ)⁻¹‖ < 1
    rw [norm_inv, Real.norm_natCast]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  have h := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    hn P).2
  have h' := (hasSum_subtype_iff_indicator (f := invHom) (s := Nat.factoredNumbers P)).mp h
  have hle := sum_le_hasSum K (fun i _ => Set.indicator_nonneg
    (fun m _ => inv_nonneg.mpr (Nat.cast_nonneg m)) i) h'
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun k hk => ?_)) hle
  rw [Set.indicator_of_mem (hK k hk)]
  rfl

/-- **`∏_{p ∣ s}(1 − 1/p)⁻¹ = s/φ(s)`** (`s ≥ 1`), from `φ(s)∏p = s∏(p−1)`. -/
theorem prod_inv_eq (s : ℕ) (hs : 1 ≤ s) :
    ∏ p ∈ s.primeFactors with p.Prime, (1 - (p : ℝ)⁻¹)⁻¹ = s / s.totient := by
  have hf : (s.primeFactors.filter fun p => p.Prime) = s.primeFactors :=
    Finset.filter_true_of_mem fun p hp => Nat.prime_of_mem_primeFactors hp
  rw [hf]
  have e1 : ∀ p ∈ s.primeFactors, (1 - (p : ℝ)⁻¹)⁻¹ = (p : ℝ) / ((p - 1 : ℕ) : ℝ) := by
    intro p hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
    rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_le, Nat.cast_one]
    have h0 : (p : ℝ) - 1 ≠ 0 := by linarith
    have h1 : (p : ℝ) ≠ 0 := by linarith
    field_simp
  rw [Finset.prod_congr rfl e1, Finset.prod_div_distrib]
  have key := Nat.totient_mul_prod_primeFactors s
  have hkey : (s.totient : ℝ) * ∏ p ∈ s.primeFactors, (p : ℝ) =
      (s : ℝ) * ∏ p ∈ s.primeFactors, ((p - 1 : ℕ) : ℝ) := by
    have h := congrArg (Nat.cast : ℕ → ℝ) key
    rw [Nat.cast_mul, Nat.cast_prod, Nat.cast_mul, Nat.cast_prod] at h
    exact h
  have hφ : (0 : ℝ) < s.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hq : (0 : ℝ) < ∏ p ∈ s.primeFactors, ((p - 1 : ℕ) : ℝ) := by
    refine Finset.prod_pos fun p hp => ?_
    have := (Nat.prime_of_mem_primeFactors hp).two_le
    exact_mod_cast (by omega : 0 < p - 1)
  rw [div_eq_div_iff hq.ne' hφ.ne']
  linarith

/-- **`rad(m) = ∏_{p ∣ m} p`**. -/
def rad (m : ℕ) : ℕ := ∏ p ∈ m.primeFactors, p

/-- `rad m` is squarefree, so `μ²(rad m)/φ(rad m) = 1/φ(rad m)`. -/
theorem gt_rad (m : ℕ) : gt (rad m) = ((rad m).totient : ℝ)⁻¹ := by
  have hsf : Squarefree (rad m) := by
    unfold rad
    refine Finset.squarefree_prod_of_pairwise_isCoprime ?_ fun p hp =>
      (Nat.prime_of_mem_primeFactors hp).prime.squarefree
    intro p hp q hq hpq
    exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes
      (Nat.prime_of_mem_primeFactors hp) (Nat.prime_of_mem_primeFactors hq)).mpr hpq)
  unfold gt
  rw [moebius_apply_of_squarefree hsf]
  push_cast
  rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow, one_div]

/-- **One fiber of the radical**: `∑_{m ≤ n, rad m = s} 1/m ≤ 1/φ(s)` (`s ≥ 1`): `m = s·(m/s)`
with `m/s` factored over the primes of `s`. -/
theorem fiber_le (n s : ℕ) (hs : 1 ≤ s) :
    ∑ m ∈ (Finset.Icc 1 n).filter (fun m => rad m = s), (m : ℝ)⁻¹ ≤ ((s.totient : ℝ))⁻¹ := by
  classical
  set F := (Finset.Icc 1 n).filter (fun m => rad m = s) with hF
  have hsm : ∀ m ∈ F, s ∣ m := by
    intro m hm
    have h := (Finset.mem_filter.mp hm).2
    rw [← h]
    exact Nat.prod_primeFactors_dvd m
  have hinj : Set.InjOn (fun m => m / s) ↑F := by
    intro a ha b hb hab
    simp only at hab
    rw [← Nat.mul_div_cancel' (hsm a ha), ← Nat.mul_div_cancel' (hsm b hb), hab]
  have e1 : ∑ m ∈ F, (m : ℝ)⁻¹ = (s : ℝ)⁻¹ * ∑ k ∈ F.image (fun m => m / s), (k : ℝ)⁻¹ := by
    rw [Finset.sum_image hinj, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    conv_lhs => rw [← Nat.mul_div_cancel' (hsm m hm)]
    push_cast
    rw [mul_inv]
  have hK : ∀ k ∈ F.image (fun m => m / s), k ∈ Nat.factoredNumbers s.primeFactors := by
    intro k hk
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨hm1, hms⟩ := Finset.mem_filter.mp hm
    have hm0 : 1 ≤ m := (Finset.mem_Icc.mp hm1).1
    have hdvd := hsm m hm
    rw [Nat.mem_factoredNumbers']
    intro p hp hpk
    have hpm : p ∣ m := dvd_trans hpk (Nat.div_dvd_of_dvd hdvd)
    rw [← hms]
    unfold rad
    rw [Nat.primeFactors_prod fun q hq => Nat.prime_of_mem_primeFactors hq]
    exact Nat.mem_primeFactors.mpr ⟨hp, hpm, by omega⟩
  rw [e1]
  have hb := sum_inv_le_prod s.primeFactors _ hK
  rw [prod_inv_eq s hs] at hb
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  calc (s : ℝ)⁻¹ * ∑ k ∈ F.image (fun m => m / s), (k : ℝ)⁻¹
      ≤ (s : ℝ)⁻¹ * ((s : ℝ) / s.totient) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = ((s.totient : ℝ))⁻¹ := by
      field_simp

/-- **`∑_{1 ≤ m ≤ n} 1/m ≤ G(n)`** (`eq:coro`, 2643-2649): the fibers of the radical. -/
theorem sum_inv_le_gQ (n : ℕ) : ∑ m ∈ Finset.Icc 1 n, (m : ℝ)⁻¹ ≤ gQ 1 (n : ℝ) := by
  classical
  have hmap : ∀ m ∈ Finset.Icc 1 n, rad m ∈ sq 1 (n : ℝ) := by
    intro m hm
    have h1 := (Finset.mem_Icc.mp hm).1
    have h2 := (Finset.mem_Icc.mp hm).2
    have hle : rad m ≤ m := Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd m)
    have hpos : 0 < rad m := Finset.prod_pos fun p hp => (Nat.prime_of_mem_primeFactors hp).pos
    refine sq_mem hpos ?_ (Nat.coprime_one_right _)
    exact_mod_cast le_trans hle h2
  rw [← Finset.sum_fiberwise_of_maps_to hmap, gQ_eq_gt]
  refine Finset.sum_le_sum fun s hs => ?_
  have hs1 : 1 ≤ s := (mem_sq hs).1
  obtain ⟨m, -, rfl⟩ | hempty : (∃ m ∈ Finset.Icc 1 n, rad m = s) ∨
      ((Finset.Icc 1 n).filter (fun m => rad m = s) = ∅) := by
    by_cases h : ∃ m ∈ Finset.Icc 1 n, rad m = s
    · exact Or.inl h
    · refine Or.inr (Finset.filter_eq_empty_iff.mpr fun m hm hms => h ⟨m, hm, hms⟩)
  · rw [gt_rad]
    exact fiber_le n (rad m) hs1
  · rw [hempty, Finset.sum_empty]
    exact gt_nonneg s

/-- **`eq:coro`**: `log R < G(R)` for `R ≥ 1` (`G(R) ≥ ∑_{r ≤ R} 1/r ≥ log(⌊R⌋ + 1)`). -/
theorem log_lt_gQ (R : ℝ) (hR : 1 ≤ R) : Real.log R < gQ 1 R := by
  set n := ⌊R⌋₊ with hn
  have hR0 : 0 < R := by linarith
  have h1 : R < (n : ℝ) + 1 := Nat.lt_floor_add_one R
  have h2 : Real.log R < Real.log ((n : ℝ) + 1) := Real.log_lt_log hR0 h1
  have h3 := log_add_one_le_harmonic n
  have h4 : (harmonic n : ℝ) = ∑ m ∈ Finset.Icc 1 n, (m : ℝ)⁻¹ := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    rfl
  have h5 := sum_inv_le_gQ n
  have h6 : gQ 1 (n : ℝ) = gQ 1 R := by
    unfold gQ
    rw [Nat.floor_natCast]
  push_cast at h3
  linarith

end Principia.Common.PSieve
