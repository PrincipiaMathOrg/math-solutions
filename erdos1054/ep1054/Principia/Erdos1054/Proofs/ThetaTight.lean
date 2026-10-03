/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Erdos1054.Spine
import Principia.Erdos1054.Basic
import Principia.Erdos1054.Density
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false

/-!
# EP1054 §6: the cofactor-two range and the tightness equivalence (`ThetaTight` package)

Discharges thirteen obligations of `Principia.Erdos1054.Spine` (paper
`Campaigns/Erdos-1054/collab-paper/EP1054.tex`, lines 2564–2717).

Leaves (from the definitions and Mathlib alone):
* `leaf_Eq_F2Aliquot` — `F₂(d) = s(2d)` (lines 2577–2580): the only divisor of `2d` above `d` is
  `2d`, so `σ(2d) = F₂(d) + 2d` (`sig_two_mul`).
* `leaf_Coverage_Step_G2Decomp` — `G₂ = σ(ℕ) ∪ F₂(ℕ)` (lines 2631–2634): `F₁(d) = σ(d)`.
* `leaf_Coverage_Step_P2Values` — `Λ(2) = 2`, `P₂ = 4`, `P₂# = 6`, `δ₂ = 1/3` (lines 2636–2637).

Links (from exactly the dependencies the spine names):
* `link_Eq_F2OddNegligible` (lines 2587–2594) — from `Std_sigma_odd_iff`, with `C = 2`: an odd
  value `F₂(d)` forces `σ(2d)` odd, so `d = j²` or `d = 2j²`, and `d ≤ F₂(d) ≤ X` (`F_ge`) puts
  `j ≤ √X`. (`Eq_F2Aliquot` is taken but its content is re-derived as `sig_two_mul`.)
* `link_Eq_OddUntouchables` (lines 2596–2605) — from `Cite_MV_exceptional`: an odd untouchable
  `N ≥ 3` has `N − 1` in the Montgomery–Vaughan exceptional set or `N − 1 = 2p`, since
  `s(pq) = 1 + p + q` for primes `p < q` (`aliquot_mul_primes`); `N = 1 = s(2)` is not
  untouchable. The `2p` are counted by `π(X) ≤ 8 X / log X`
  (Mathlib `Chebyshev.pi_le_log4_mul_div`).
* `link_Coverage_Step_EvenUntouchables` (lines 2610–2612) — from `Eq_OddUntouchables` and
  `Cite_ChenZhao`.
* `link_Coverage_Disp_F2Count` (lines 2612–2619) — `F₂(ℕ) ⊆ odd part ∪ (evens ∖ even untouchables)`.
* `link_Prop_ThetaTwo` (lines 2569–2620) — the upper limit of the count.
* `link_Coverage_Step_UpperDensG2` (lines 2635–2636) and `link_Cor_EtaTwo` (lines 2623–2645).
* `link_Coverage_Disp_TailLeCompl` (lines 2689–2700) — from `Intro_RcntFormula`:
  `ν_X((E, ∞]) ≤ R(X)⁻¹ #{N ≤ X : N ∉ G_E}` (`nuX_Ioi_le`) and `R(X) = ⌊X⌋ − 2`.
* `link_Coverage_Disp_ComplLeTail` (lines 2706–2713) — from `Lem_Moment` (its `eq:large-count`
  clause, `A = T`) and `Eq_ExactRepresentability` (the unrepresented integers `0, 2, 5` form a
  finite set); the tail density is compared with `limsup ν_X((T, ∞])` along integer `X`
  (`nuX_Ioi_ge`, `R(n) ≤ n`).
* `link_Prop_TightnessEquivalence` (lines 2674–2717) — `nuTight_of_criterion` (the tail beyond
  `E` is uniformly small for `X ≥ X₁`; for `1 ≤ X < X₁` every ratio `f(N)/N`, `N ≤ X₁`, is below
  `∑_{M ≤ X₁} f(M)`, so `ν_X((T, ∞]) = 0` for large `T`) and `criterion_of_nuTight`
  (`Disp_ComplLeTail` at `k = 2`: first `E → ∞`, then `T → ∞`); the other two equivalences are
  `Fact_UpperDensCompl` and the definition of `Conj_BoundedCofactorWeak`.
-/

namespace Principia.Erdos1054.Proofs.ThetaTight

open Finset Filter
open Principia.Erdos1054
open scoped Topology ENNReal

/-- `σ(e d) = F_e(d) + ∑_{r ∣ e d, r > d} r`. -/
theorem sig_mul_eq_F_add (e d : ℕ) :
    sig (e * d) = F e d + ∑ r ∈ (e * d).divisors.filter (fun r => ¬ r ≤ d), r := by
  show ArithmeticFunction.sigma 1 (e * d) = _
  rw [ArithmeticFunction.sigma_one_apply, F, Finset.sum_filter_add_sum_filter_not]

/-- The divisors of `2d` exceeding `d` are exactly `2d`. -/
theorem filter_gt_divisors_two_mul (d : ℕ) (hd : 1 ≤ d) :
    (2 * d).divisors.filter (fun r => ¬ r ≤ d) = {2 * d} := by
  ext r
  simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_singleton, not_le]
  constructor
  · rintro ⟨⟨⟨k, hk⟩, -⟩, hr⟩
    have hk2 : k < 2 := by
      by_contra h
      have h' : 2 ≤ k := not_lt.1 h
      nlinarith
    interval_cases k <;> omega
  · rintro rfl
    exact ⟨⟨dvd_refl _, by omega⟩, by omega⟩

/-- `σ(2d) = F_2(d) + 2d`. -/
theorem sig_two_mul (d : ℕ) (hd : 1 ≤ d) : sig (2 * d) = F 2 d + 2 * d := by
  rw [sig_mul_eq_F_add 2 d, filter_gt_divisors_two_mul d hd, Finset.sum_singleton]

/-- `σ(n) = F_1(n)`: every divisor of `1 · n` is `≤ n`. -/
theorem sig_eq_F_one (n : ℕ) : sig n = F 1 n := by
  show ArithmeticFunction.sigma 1 n = F 1 n
  rw [ArithmeticFunction.sigma_one_apply, F, one_mul, Finset.filter_true_of_mem]
  intro d hd
  exact Nat.divisor_le hd

theorem filter_divisors_mul_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q) :
    (p * q).divisors.filter (· ≤ q) = {1, p, q} := by
  have hpq0 : p * q ≠ 0 := (Nat.mul_pos hp.pos hq.pos).ne'
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨hd, -⟩, hle⟩
    obtain ⟨d₁, d₂, h₁, h₂, rfl⟩ := dvd_mul.mp hd
    rcases (Nat.dvd_prime hp).mp h₁ with rfl | rfl <;>
      rcases (Nat.dvd_prime hq).mp h₂ with rfl | rfl
    · left; ring
    · right; right; ring
    · right; left; ring
    · exfalso
      have h2 := hp.two_le
      have hq0 := hq.pos
      nlinarith
  · rintro (rfl | rfl | rfl)
    · exact ⟨⟨one_dvd _, hpq0⟩, hq.one_lt.le⟩
    · exact ⟨⟨dvd_mul_right _ _, hpq0⟩, hpq.le⟩
    · exact ⟨⟨dvd_mul_left _ _, hpq0⟩, le_rfl⟩

theorem F_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q) :
    F p q = 1 + p + q := by
  unfold F
  rw [filter_divisors_mul_primes hp hq hpq, Finset.sum_insert, Finset.sum_pair hpq.ne]
  · ring
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hp.one_lt.ne, hq.one_lt.ne⟩

theorem filter_gt_divisors_mul_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q) :
    (p * q).divisors.filter (fun r => ¬ r ≤ q) = {p * q} := by
  have hpq0 : p * q ≠ 0 := (Nat.mul_pos hp.pos hq.pos).ne'
  ext r
  simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_singleton, not_le]
  constructor
  · rintro ⟨⟨hr, -⟩, hlt⟩
    obtain ⟨d₁, d₂, h₁, h₂, rfl⟩ := dvd_mul.mp hr
    rcases (Nat.dvd_prime hp).mp h₁ with rfl | rfl <;>
      rcases (Nat.dvd_prime hq).mp h₂ with rfl | rfl
    · have := hq.one_lt
      omega
    · omega
    · omega
    · rfl
  · rintro rfl
    refine ⟨⟨dvd_refl _, hpq0⟩, ?_⟩
    have := hp.two_le
    nlinarith

/-- `s(pq) = 1 + p + q` for primes `p < q`. -/
theorem aliquot_mul_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q) :
    aliquot (p * q) = 1 + p + q := by
  have h := sig_mul_eq_F_add p q
  rw [filter_gt_divisors_mul_primes hp hq hpq, Finset.sum_singleton, F_primes hp hq hpq] at h
  show sig (p * q) - p * q = 1 + p + q
  omega

/-- `s(2) = 1`. -/
theorem aliquot_two : aliquot 2 = 1 := by
  have h := sig_two_mul 1 le_rfl
  have h1 : F 2 1 = 1 := by decide
  show sig 2 - 2 = 1
  rw [h1] at h
  norm_num at h
  omega

/-! ## Counting helpers for `prop:theta-two` -/

/-- The odd part of `F₂(ℕ)`. -/
def oddF2 : Set ℕ := {N : ℕ | Odd N ∧ N ∈ Frange 2}

/-- The odd untouchables. -/
def oddU : Set ℕ := {N : ℕ | Odd N ∧ N ∈ Coverage.untouchable}

/-- The even untouchables. -/
def evenU : Set ℕ := {N : ℕ | Even N ∧ N ∈ Coverage.untouchable}

/-- The even integers. -/
def evens : Set ℕ := {N : ℕ | 2 ∣ N}

/-- The Montgomery–Vaughan exceptional set: even integers that are not a sum of two primes. -/
def mvSet : Set ℕ := {n : ℕ | Even n ∧ ¬ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p + q}

/-- `#(A \ B) + #B ≤ #A` for `B ⊆ A`. -/
theorem cnt_sdiff_add_le {A B : Set ℕ} (h : B ⊆ A) (X : ℝ) :
    cnt (A \ B) X + cnt B X ≤ cnt A X := by
  classical
  unfold cnt
  rw [← Finset.card_union_of_disjoint]
  · apply Finset.card_le_card
    intro n hn
    rw [Finset.mem_union, mem_cntFinset, mem_cntFinset] at hn
    rw [mem_cntFinset]
    rcases hn with h1 | h1
    · exact ⟨h1.1, h1.2.1⟩
    · exact ⟨h1.1, h h1.2⟩
  · rw [Finset.disjoint_left]
    intro n h1 h2
    exact (mem_cntFinset.1 h1).2.2 (mem_cntFinset.1 h2).2

/-- The odd values of `F₂` up to `X` come from `d = j²` or `d = 2 j²` with `j ≤ √X`. -/
theorem cnt_oddF2_le (hsig : Std_sigma_odd_iff) (X : ℝ) :
    cnt oddF2 X ≤ 2 * Nat.sqrt ⌊X⌋₊ := by
  classical
  set n := ⌊X⌋₊ with hn
  set m := Nat.sqrt n with hm
  set T : Finset ℕ :=
    (Icc 1 m).image (fun j => j ^ 2) ∪ (Icc 1 m).image (fun j => 2 * j ^ 2) with hT
  have hsub : (Icc 1 n).filter (· ∈ oddF2) ⊆ T.image (fun d => F 2 d) := by
    intro N hN
    rw [mem_filter, mem_Icc] at hN
    obtain ⟨⟨_, hNn⟩, hodd, d, hd, rfl⟩ := hN
    have hFd : d ≤ F 2 d := F_ge 2 d (by norm_num) hd
    have hs := sig_two_mul d hd
    have hsodd : Odd (sig (2 * d)) := by
      rw [hs]
      exact hodd.add_even (even_two_mul d)
    refine mem_image.2 ⟨d, ?_, rfl⟩
    rcases (hsig (2 * d) (by omega)).1 hsodd with ⟨r, hr⟩ | ⟨j, hj⟩
    · have h2r : 2 ∣ r := by
        have h2 : 2 ∣ r * r := hr ▸ dvd_mul_right 2 d
        rcases (Nat.Prime.dvd_mul Nat.prime_two).1 h2 with h | h <;> exact h
      obtain ⟨j, rfl⟩ := h2r
      have hdj : d = 2 * j ^ 2 := by nlinarith
      have hj1 : 1 ≤ j := by
        rcases Nat.eq_zero_or_pos j with h0 | h0
        · subst h0
          simp at hdj
          omega
        · exact h0
      have hjm : j ≤ m := Nat.le_sqrt.2 (by nlinarith)
      exact mem_union.2 (Or.inr (mem_image.2 ⟨j, mem_Icc.2 ⟨hj1, hjm⟩, hdj.symm⟩))
    · have hdj : d = j ^ 2 := by omega
      have hj1 : 1 ≤ j := by
        rcases Nat.eq_zero_or_pos j with h0 | h0
        · subst h0
          simp at hdj
          omega
        · exact h0
      have hjm : j ≤ m := Nat.le_sqrt.2 (by nlinarith)
      exact mem_union.2 (Or.inl (mem_image.2 ⟨j, mem_Icc.2 ⟨hj1, hjm⟩, hdj.symm⟩))
  calc cnt oddF2 X = ((Icc 1 n).filter (· ∈ oddF2)).card := rfl
    _ ≤ (T.image (fun d => F 2 d)).card := card_le_card hsub
    _ ≤ T.card := card_image_le
    _ ≤ ((Icc 1 m).image (fun j => j ^ 2)).card + ((Icc 1 m).image (fun j => 2 * j ^ 2)).card :=
        card_union_le _ _
    _ ≤ (Icc 1 m).card + (Icc 1 m).card := add_le_add card_image_le card_image_le
    _ = 2 * m := by rw [Nat.card_Icc]; omega

/-- Odd untouchables: `N − 1` is a Montgomery–Vaughan exception or twice a prime. -/
theorem cnt_oddU_le (X : ℝ) :
    cnt oddU X ≤ cnt mvSet X + Nat.primeCounting ⌊X⌋₊ := by
  classical
  have hmaps : ∀ n ∈ (Icc 1 ⌊X⌋₊).filter (· ∈ oddU),
      n - 1 ∈ ((Icc 1 ⌊X⌋₊).filter (· ∈ mvSet)) ∪ (Nat.primesLE ⌊X⌋₊).image (2 * ·) := by
    intro n hn
    rw [mem_filter, mem_Icc] at hn
    obtain ⟨⟨hn1, hnX⟩, hodd, hnU⟩ := hn
    have hn3 : 3 ≤ n := by
      obtain ⟨k, rfl⟩ := hodd
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · exact absurd aliquot_two (hnU 2 (by norm_num))
      · omega
    rw [mem_union, mem_filter, mem_Icc, mem_image]
    by_cases hgold : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n - 1 = p + q
    · right
      obtain ⟨p, q, hp, hq, hpq⟩ := hgold
      by_cases hne : p = q
      · subst hne
        exact ⟨p, Nat.mem_primesLE.mpr ⟨by omega, hp⟩, by omega⟩
      · exfalso
        rcases lt_or_gt_of_ne hne with h | h
        · exact hnU (p * q) (Nat.mul_pos hp.pos hq.pos)
            (by rw [aliquot_mul_primes hp hq h]; omega)
        · exact hnU (q * p) (Nat.mul_pos hq.pos hp.pos)
            (by rw [aliquot_mul_primes hq hp h]; omega)
    · left
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      show Even (n - 1) ∧ ¬ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n - 1 = p + q
      obtain ⟨k, hk⟩ := hodd
      exact ⟨⟨k, by omega⟩, hgold⟩
  have hinj : ((Icc 1 ⌊X⌋₊).filter (· ∈ oddU) : Set ℕ).InjOn (fun n => n - 1) := by
    intro a ha b hb hab
    simp only [coe_filter, mem_Icc, Set.mem_setOf_eq] at ha hb
    simp only at hab
    omega
  calc cnt oddU X = ((Icc 1 ⌊X⌋₊).filter (· ∈ oddU)).card := rfl
    _ ≤ (((Icc 1 ⌊X⌋₊).filter (· ∈ mvSet)) ∪ (Nat.primesLE ⌊X⌋₊).image (2 * ·)).card :=
        card_le_card_of_injOn (fun n => n - 1) hmaps hinj
    _ ≤ ((Icc 1 ⌊X⌋₊).filter (· ∈ mvSet)).card + ((Nat.primesLE ⌊X⌋₊).image (2 * ·)).card :=
        card_union_le _ _
    _ ≤ ((Icc 1 ⌊X⌋₊).filter (· ∈ mvSet)).card + (Nat.primesLE ⌊X⌋₊).card :=
        Nat.add_le_add_left card_image_le _
    _ = cnt mvSet X + Nat.primeCounting ⌊X⌋₊ := by
        rw [Nat.primesLE_card_eq_primeCounting]; rfl

/-- `π(X) ≤ 8 X / log X` for `X ≥ 3` (from Mathlib's Chebyshev bound). -/
theorem primeCounting_le (X : ℝ) (hX : 3 ≤ X) :
    (Nat.primeCounting ⌊X⌋₊ : ℝ) ≤ 8 * (X / Real.log X) := by
  have hX1 : 1 < X := by linarith
  have hlogpos : 0 < Real.log X := Real.log_pos hX1
  have h := Chebyshev.pi_le_log4_mul_div hX1
  rw [Real.log_sqrt (by linarith)] at h
  have hsq : √X * Real.log X ≤ 2 * X := by
    have h1 : Real.log √X ≤ √X - 1 :=
      Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr (by linarith))
    rw [Real.log_sqrt (by linarith)] at h1
    have h2 : √X * √X = X := Real.mul_self_sqrt (by linarith)
    have h3 : 0 ≤ √X := Real.sqrt_nonneg X
    nlinarith
  have hlog4 : Real.log 4 ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
    linarith
  have hsqrt : √X ≤ 2 * (X / Real.log X) := by
    rw [mul_div_assoc', le_div_iff₀ hlogpos]
    linarith
  have h4 : Real.log 4 * X / (Real.log X / 2) = 2 * Real.log 4 * (X / Real.log X) := by
    field_simp
  have hXL : 0 ≤ X / Real.log X := div_nonneg (by linarith) hlogpos.le
  rw [h4] at h
  nlinarith

/-- A count bounded by `C X^{1-c} + 8 X / log X` (`c > 0`) has density zero. -/
theorem densZero_of_le_rpow_add {S : Set ℕ} {c C : ℝ} (hc : 0 < c)
    (h : ∀ X : ℝ, 3 ≤ X → (cnt S X : ℝ) ≤ C * X ^ (1 - c) + 8 * (X / Real.log X)) :
    DensZero S := by
  rw [densZero_iff_exists_real]
  intro ε hε
  have hC'0 : 0 ≤ max C 0 := le_max_right _ _
  have t1 : Tendsto (fun X : ℝ => max C 0 * X ^ (-c)) atTop (𝓝 0) := by
    have := (tendsto_rpow_neg_atTop hc).const_mul (max C 0)
    rwa [mul_zero] at this
  have t2 : Tendsto (fun X : ℝ => 8 * (Real.log X)⁻¹) atTop (𝓝 0) := by
    have := (tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop).const_mul (8 : ℝ)
    rw [mul_zero] at this
    exact this
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.1 ((t1.eventually (gt_mem_nhds (half_pos hε))).and
    ((t2.eventually (gt_mem_nhds (half_pos hε))).and (eventually_ge_atTop (3 : ℝ))))
  refine ⟨X₀, fun X hX => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hX₀ X hX
  have hXpos : 0 < X := by linarith
  have hsplit : X ^ (1 - c) = X ^ (-c) * X := by
    rw [show 1 - c = -c + 1 by ring, Real.rpow_add hXpos, Real.rpow_one]
  have hrpow : 0 ≤ X ^ (-c) := Real.rpow_nonneg hXpos.le _
  have hA : C * X ^ (1 - c) ≤ ε / 2 * X := by
    rw [hsplit]
    calc C * (X ^ (-c) * X) ≤ max C 0 * (X ^ (-c) * X) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (mul_nonneg hrpow hXpos.le)
      _ = (max C 0 * X ^ (-c)) * X := by ring
      _ ≤ ε / 2 * X := mul_le_mul_of_nonneg_right h1.le hXpos.le
  have hB : 8 * (X / Real.log X) ≤ ε / 2 * X := by
    calc 8 * (X / Real.log X) = (8 * (Real.log X)⁻¹) * X := by rw [div_eq_mul_inv]; ring
      _ ≤ ε / 2 * X := mul_le_mul_of_nonneg_right h2.le hXpos.le
  have := h X h3
  linarith

/-! ## The empirical measures `ν_X` as normalised counts -/

open Classical in
/-- `ν_X(s)` of a measurable set, as a normalised sum over `N ∈ [1, X]`. -/
theorem nuX_apply' (X : ℝ) {s : Set ℝ≥0∞} (hs : MeasurableSet s) :
    nuX X s = (Rcnt X : ℝ≥0∞)⁻¹ *
      ∑ N ∈ Finset.Icc 1 ⌊X⌋₊, if N ∈ R then s.indicator 1 (ratioE N) else 0 := by
  rw [nuX, MeasureTheory.Measure.smul_apply, MeasureTheory.Measure.finsetSum_apply, smul_eq_mul,
    Finset.sum_filter]
  congr 1
  refine Finset.sum_congr rfl fun N _ => ?_
  split_ifs
  · exact MeasureTheory.Measure.dirac_apply' _ hs
  · rfl

open Classical in
/-- `#(S ∩ [1, X])` as a sum of indicators in `ℝ≥0∞`. -/
theorem natCast_cnt_eq_sum (S : Set ℕ) (X : ℝ) :
    ((cnt S X : ℕ) : ℝ≥0∞) = ∑ N ∈ Finset.Icc 1 ⌊X⌋₊, if N ∈ S then (1 : ℝ≥0∞) else 0 := by
  unfold cnt
  rw [Finset.natCast_card_filter]

/-- `N ∈ G_E ⟹ f(N) ≤ E N` (EP1054.tex lines 2690–2693: `f(N) ≤ e d ≤ E N`). -/
theorem f_le_mul_of_mem_Gcov {E N : ℕ} (hN : N ∈ Gcov E) : f N ≤ E * N := by
  obtain ⟨e, d, he1, heE, hd, rfl⟩ := hN
  calc f (F e d) ≤ e * d := f_le_of_F e d _ he1 hd rfl
    _ ≤ E * F e d := Nat.mul_le_mul heE (F_ge e d he1 hd)

/-- `N ∈ G_E ⟹ f(N)/N ≤ E`. -/
theorem ratioE_le_of_mem_Gcov {E N : ℕ} (hN : N ∈ Gcov E) : ratioE N ≤ (E : ℝ≥0∞) := by
  have h := f_le_mul_of_mem_Gcov hN
  unfold ratioE
  rw [← ENNReal.ofReal_natCast E]
  apply ENNReal.ofReal_le_ofReal
  rcases Nat.eq_zero_or_pos N with h0 | hpos
  · subst h0
    simp
  · rw [div_le_iff₀ (by exact_mod_cast hpos)]
    exact_mod_cast h

/-- `m⁻¹ c ≤ a` in `ℝ≥0∞` from `c ≤ a m` in `ℝ`. -/
theorem inv_mul_natCast_le_ofReal {m c : ℕ} {a : ℝ} (hm : 0 < m) (h : (c : ℝ) ≤ a * m) :
    ((m : ℝ≥0∞))⁻¹ * (c : ℝ≥0∞) ≤ ENNReal.ofReal a := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  rw [← ENNReal.div_eq_inv_mul, ← ENNReal.ofReal_natCast c, ← ENNReal.ofReal_natCast m,
    ← ENNReal.ofReal_div_of_pos hm']
  exact ENNReal.ofReal_le_ofReal ((div_le_iff₀ hm').2 h)

/-- `a ≤ m⁻¹ c` in `ℝ≥0∞` from `a m ≤ c` in `ℝ`. -/
theorem ofReal_le_inv_mul_natCast {m c : ℕ} {a : ℝ} (hm : 0 < m) (h : a * m ≤ c) :
    ENNReal.ofReal a ≤ ((m : ℝ≥0∞))⁻¹ * (c : ℝ≥0∞) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  rw [← ENNReal.div_eq_inv_mul, ← ENNReal.ofReal_natCast c, ← ENNReal.ofReal_natCast m,
    ← ENNReal.ofReal_div_of_pos hm']
  exact ENNReal.ofReal_le_ofReal ((le_div_iff₀ hm').2 h)

/-- The tail beyond `E` only sees integers outside `G_E`:
`ν_X((E, ∞]) ≤ R(X)⁻¹ #{N ≤ X : N ∉ G_E}`. -/
theorem nuX_Ioi_le (E : ℕ) (X : ℝ) :
    nuX X (Set.Ioi (E : ℝ≥0∞)) ≤
      (Rcnt X : ℝ≥0∞)⁻¹ * (cnt {N : ℕ | N ∉ Gcov E} X : ℝ≥0∞) := by
  rw [nuX_apply' X measurableSet_Ioi, natCast_cnt_eq_sum]
  refine mul_le_mul' le_rfl (Finset.sum_le_sum fun N _ => ?_)
  by_cases h1 : N ∈ R
  · rw [if_pos h1]
    by_cases h2 : N ∈ Gcov E
    · have h3 : N ∉ {N : ℕ | N ∉ Gcov E} := fun h => h h2
      rw [if_neg h3, Set.indicator_of_notMem]
      rw [Set.mem_Ioi, not_lt]
      exact ratioE_le_of_mem_Gcov h2
    · have h3 : N ∈ {N : ℕ | N ∉ Gcov E} := h2
      rw [if_pos h3]
      exact Set.indicator_apply_le' (fun _ => le_rfl) (fun _ => zero_le)
  · rw [if_neg h1]
    exact zero_le

/-- The tail beyond `T` sees every large ratio:
`R(X)⁻¹ #{N ≤ X : N ∈ 𝓡, f(N) > T N} ≤ ν_X((T, ∞])`. -/
theorem nuX_Ioi_ge (T : ℝ) (hT : 0 ≤ T) (X : ℝ) :
    (Rcnt X : ℝ≥0∞)⁻¹ * (cnt (largeRatioSet T) X : ℝ≥0∞) ≤
      nuX X (Set.Ioi (ENNReal.ofReal T)) := by
  rw [nuX_apply' X measurableSet_Ioi, natCast_cnt_eq_sum]
  refine mul_le_mul' le_rfl (Finset.sum_le_sum fun N hN => ?_)
  by_cases h1 : N ∈ largeRatioSet T
  · obtain ⟨hR, hlt⟩ := h1
    have hN1 : 1 ≤ N := (Finset.mem_Icc.1 hN).1
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
    have hTr : T < (f N : ℝ) / N := by
      rw [lt_div_iff₀ hNpos]
      linarith
    have hmem : ratioE N ∈ Set.Ioi (ENNReal.ofReal T) := by
      rw [Set.mem_Ioi]
      unfold ratioE
      rw [ENNReal.ofReal_lt_ofReal_iff']
      exact ⟨hTr, lt_of_le_of_lt hT hTr⟩
    have h1' : N ∈ largeRatioSet T := ⟨hR, hlt⟩
    simp only [if_pos h1', if_pos hR, Set.indicator_of_mem hmem, Pi.one_apply, le_refl]
  · rw [if_neg h1]
    exact zero_le

/-- `R(X) ≤ ⌊X⌋`. -/
theorem Rcnt_le_floor (X : ℝ) : Rcnt X ≤ ⌊X⌋₊ := cnt_le_floor R X

/-! ## The two directions of `prop:tightness-equivalence` -/

/-- Criterion ⟹ tight: the tail beyond `E` is small for large `X` (`Disp_TailLeCompl`), and for
`X` in a bounded interval the finitely many ratios have a common bound. -/
theorem nuTight_of_criterion (hTLC : Coverage.Disp_TailLeCompl) (hcrit : Eq_TightnessCriterion) :
    Coverage.NuTight := by
  unfold Coverage.NuTight
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨r, -, h0r, hrε⟩ := ENNReal.lt_iff_exists_real_btwn.1 hε
  have hrpos : 0 < r := ENNReal.ofReal_pos.1 h0r
  obtain ⟨E, hEr, hE1⟩ :=
    ((hcrit.eventually (gt_mem_nhds hrpos)).and (eventually_ge_atTop 1)).exists
  have hlim : limsup (fun X : ℝ => nuX X (Set.Ioi (E : ℝ≥0∞))) atTop < ENNReal.ofReal r :=
    lt_of_le_of_lt (hTLC E hE1) ((ENNReal.ofReal_lt_ofReal_iff hrpos).2 hEr)
  obtain ⟨X₁, hX₁⟩ := eventually_atTop.1 (eventually_lt_of_limsup_lt hlim)
  have hbound : ∀ N : ℕ, N ≤ ⌊X₁⌋₊ →
      (f N : ℝ) / N ≤ ∑ M ∈ Finset.range (⌊X₁⌋₊ + 1), (f M : ℝ) := by
    intro N hN
    have hsum : (f N : ℝ) ≤ ∑ M ∈ Finset.range (⌊X₁⌋₊ + 1), (f M : ℝ) :=
      Finset.single_le_sum (f := fun M => (f M : ℝ)) (fun M _ => Nat.cast_nonneg (f M))
        (Finset.mem_range.2 (by omega))
    rcases Nat.eq_zero_or_pos N with h0 | hpos
    · subst h0
      rw [Nat.cast_zero, div_zero]
      exact le_trans (Nat.cast_nonneg _) hsum
    · exact le_trans (div_le_self (Nat.cast_nonneg _) (by exact_mod_cast hpos)) hsum
  filter_upwards [eventually_ge_atTop
    (max (E : ℝ) (∑ M ∈ Finset.range (⌊X₁⌋₊ + 1), (f M : ℝ)))] with T hT
  refine iSup₂_le fun X _ => ?_
  rcases le_or_gt X₁ X with hXX | hXX
  · have hsub : Set.Ioi (ENNReal.ofReal T) ⊆ Set.Ioi (E : ℝ≥0∞) := by
      apply Set.Ioi_subset_Ioi
      rw [← ENNReal.ofReal_natCast]
      exact ENNReal.ofReal_le_ofReal (le_trans (le_max_left _ _) hT)
    exact (MeasureTheory.measure_mono hsub).trans ((hX₁ X hXX).le.trans hrε.le)
  · have h0 : nuX X (Set.Ioi (ENNReal.ofReal T)) = 0 := by
      rw [nuX_apply' X measurableSet_Ioi, Finset.sum_eq_zero, mul_zero]
      intro N hN
      have hNX : N ≤ ⌊X₁⌋₊ := le_trans (Finset.mem_Icc.1 hN).2 (Nat.floor_mono hXX.le)
      split_ifs
      · apply Set.indicator_of_notMem
        rw [Set.mem_Ioi, not_lt]
        unfold ratioE
        exact ENNReal.ofReal_le_ofReal ((hbound N hNX).trans (le_trans (le_max_right _ _) hT))
      · rfl
    rw [h0]
    exact zero_le

/-- Tight ⟹ criterion: `Disp_ComplLeTail` at `k = 2`; first `E → ∞`, then `T → ∞`. -/
theorem criterion_of_nuTight (hCLT : Coverage.Disp_ComplLeTail) (hT : Coverage.NuTight) :
    Eq_TightnessCriterion := by
  obtain ⟨C, hC⟩ := hCLT 2 le_rfl
  unfold Eq_TightnessCriterion
  rw [tendsto_order]
  refine ⟨fun a ha => Eventually.of_forall fun E => lt_of_lt_of_le ha (upperDens_nonneg _),
    fun a ha => ?_⟩
  have ha2 : 0 < a / 2 := half_pos ha
  obtain ⟨T, hTsup, hT1⟩ := ((hT.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 ha2))).and
    (eventually_ge_atTop (1 : ℝ))).exists
  have hL : limsup (fun X : ℝ => nuX X (Set.Ioi (ENNReal.ofReal T))) atTop <
      ENNReal.ofReal (a / 2) := by
    refine lt_of_le_of_lt (limsup_le_of_le (h := ?_)) hTsup
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with X hX
    exact le_iSup₂ (f := fun (X : ℝ) (_ : 1 ≤ X) => nuX X (Set.Ioi (ENNReal.ofReal T))) X hX
  have e : (1 - ((2 : ℕ) : ℝ)) = -(1 : ℝ) := by norm_num
  have ht : Tendsto (fun E : ℕ => C * T ^ (2 + 1) * (E : ℝ) ^ (-(1 : ℝ))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun E : ℕ => (E : ℝ) ^ (-(1 : ℝ))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop one_pos).comp tendsto_natCast_atTop_atTop
    have h2 := h1.const_mul (C * T ^ (2 + 1))
    rw [mul_zero] at h2
    exact h2
  filter_upwards [ht.eventually (gt_mem_nhds ha2), eventually_ge_atTop 1] with E hE hE1
  have h := hC T hT1 E hE1
  rw [e] at h
  have h3 : ENNReal.ofReal (C * T ^ (2 + 1) * (E : ℝ) ^ (-(1 : ℝ))) < ENNReal.ofReal (a / 2) :=
    (ENNReal.ofReal_lt_ofReal_iff ha2).2 hE
  have h4 : ENNReal.ofReal (upperDens {N : ℕ | N ∉ Gcov E}) < ENNReal.ofReal a := by
    calc ENNReal.ofReal (upperDens {N : ℕ | N ∉ Gcov E})
        ≤ limsup (fun X : ℝ => nuX X (Set.Ioi (ENNReal.ofReal T))) atTop +
            ENNReal.ofReal (C * T ^ (2 + 1) * (E : ℝ) ^ (-(1 : ℝ))) := h
      _ < ENNReal.ofReal (a / 2) + ENNReal.ofReal (a / 2) := ENNReal.add_lt_add hL h3
      _ = ENNReal.ofReal a := by rw [← ENNReal.ofReal_add ha2.le ha2.le, add_halves]
  exact (ENNReal.ofReal_lt_ofReal_iff ha).1 h4

end Principia.Erdos1054.Proofs.ThetaTight

namespace Principia.Erdos1054.Proofs

open Finset Filter
open Principia.Erdos1054 Principia.Erdos1054.Proofs.ThetaTight
open scoped Topology ENNReal

/-- `eq:F2-aliquot` (EP1054.tex lines 2577–2580). -/
theorem leaf_Eq_F2Aliquot : Principia.Erdos1054.Eq_F2Aliquot := by
  intro d hd
  have h := sig_two_mul d hd
  show F 2 d = sig (2 * d) - 2 * d
  omega

/-- `G₂ = σ(ℕ) ∪ F₂(ℕ)` (EP1054.tex lines 2631–2634). -/
theorem leaf_Coverage_Step_G2Decomp : Principia.Erdos1054.Coverage.Step_G2Decomp := by
  ext N
  simp only [Gcov, Frange, Set.mem_setOf_eq, Set.mem_union]
  constructor
  · rintro ⟨e, d, he1, he2, hd, rfl⟩
    interval_cases e
    · exact Or.inl ⟨d, hd, sig_eq_F_one d⟩
    · exact Or.inr ⟨d, hd, rfl⟩
  · rintro (⟨n, hn, rfl⟩ | ⟨d, hd, rfl⟩)
    · exact ⟨1, n, le_rfl, by norm_num, hn, sig_eq_F_one n⟩
    · exact ⟨2, d, by norm_num, le_rfl, hd, rfl⟩

/-- `Λ(2) = 2`, `P₂ = 4`, `P₂# = 6`, `δ₂ = 1/3` (EP1054.tex lines 2636–2637). -/
theorem leaf_Coverage_Step_P2Values : Principia.Erdos1054.Coverage.Step_P2Values := by
  have hL : lcmUpTo (2 : ℝ) = 2 := by
    unfold lcmUpTo
    rw [Nat.floor_ofNat]
    decide
  have hP : Coverage.PA 2 = 4 := by
    unfold Coverage.PA
    rw [Nat.cast_ofNat, hL]
  refine ⟨hL, hP, ?_, ?_⟩
  · unfold primorialR
    rw [hP, Nat.cast_ofNat, Nat.floor_ofNat]
    decide
  · unfold Coverage.deltaA Delta
    rw [hP, Nat.cast_ofNat, Nat.floor_ofNat]
    have hs : (Finset.range (4 + 1)).filter Nat.Prime = {2, 3} := by decide
    rw [hs, Finset.prod_pair (by norm_num)]
    norm_num


/-- `eq:F2-odd-negligible` (EP1054.tex lines 2587–2594), with `C = 2`. -/
theorem link_Eq_F2OddNegligible : Principia.Erdos1054.Spine.Link_Eq_F2OddNegligible := by
  intro _hF2 hsig
  refine ⟨2, fun X hX => ?_⟩
  have h1 : (cnt oddF2 X : ℝ) ≤ 2 * (Nat.sqrt ⌊X⌋₊ : ℝ) := by
    exact_mod_cast cnt_oddF2_le hsig X
  have h2 : (Nat.sqrt ⌊X⌋₊ : ℝ) ≤ Real.sqrt X :=
    Real.nat_sqrt_le_real_sqrt.trans (Real.sqrt_le_sqrt (Nat.floor_le (by linarith)))
  show (cnt oddF2 X : ℝ) ≤ 2 * Real.sqrt X
  linarith

/-- `eq:odd-untouchables` (EP1054.tex lines 2596–2605). -/
theorem link_Eq_OddUntouchables : Principia.Erdos1054.Spine.Link_Eq_OddUntouchables := by
  intro hMV
  obtain ⟨c, hc, C, hC⟩ := hMV
  show DensZero oddU
  refine densZero_of_le_rpow_add hc (C := C) (fun X hX => ?_)
  have h1 : (cnt mvSet X : ℝ) ≤ C * X ^ (1 - c) := hC X (by linarith)
  have h2 := primeCounting_le X hX
  have h3 : (cnt oddU X : ℝ) ≤ cnt mvSet X + Nat.primeCounting ⌊X⌋₊ := by
    exact_mod_cast cnt_oddU_le X
  linarith

/-- Even untouchables have lower density `≥ 0.0602757` (EP1054.tex lines 2610–2612). -/
theorem link_Coverage_Step_EvenUntouchables :
    Principia.Erdos1054.Spine.Link_Coverage_Step_EvenUntouchables := by
  intro hodd hCZ ε hε
  have hCZ' : (0.0602757 : ℝ) ≤ lowerDens Coverage.untouchable := hCZ
  have hU : (0.0602757 : ℝ) - ε / 2 < lowerDens Coverage.untouchable := by linarith
  obtain ⟨X₁, h1⟩ := exists_mul_le_cnt_of_lt_lowerDens hU
  have hodd' : DensZero oddU := hodd
  obtain ⟨X₂, h2⟩ := hodd'.exists_le_mul (half_pos hε)
  refine ⟨max X₁ X₂, fun X hX => ?_⟩
  have a := h1 X (le_trans (le_max_left _ _) hX)
  have b := h2 X (le_trans (le_max_right _ _) hX)
  have hsub : Coverage.untouchable ⊆ evenU ∪ oddU := by
    intro N hN
    rcases Nat.even_or_odd N with h | h
    · exact Or.inl ⟨h, hN⟩
    · exact Or.inr ⟨h, hN⟩
  have c : (cnt Coverage.untouchable X : ℝ) ≤ cnt evenU X + cnt oddU X := by
    exact_mod_cast cnt_le_cnt_add_of_subset_union hsub X
  show (0.0602757 - ε) * X ≤ (cnt evenU X : ℝ)
  linarith

/-- The count of `F₂(ℕ)` up to `X` (EP1054.tex lines 2612–2619). -/
theorem link_Coverage_Disp_F2Count : Principia.Erdos1054.Spine.Link_Coverage_Disp_F2Count := by
  intro hF2 hodd heven ε hε
  obtain ⟨C, hC⟩ := hodd
  obtain ⟨X₁, h1⟩ := heven (ε / 2) (half_pos hε)
  have hδ : 0 < ε / 2 := half_pos hε
  refine ⟨max X₁ (max 1 ((max C 0 / (ε / 2)) ^ 2)), fun X hX => ?_⟩
  have hX1 : X₁ ≤ X := le_trans (le_max_left _ _) hX
  have hX2 : 1 ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hX
  have hX3 : (max C 0 / (ε / 2)) ^ 2 ≤ X :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hX
  have hsub : Frange 2 ⊆ oddF2 ∪ (evens \ evenU) := by
    intro N hN
    rcases Nat.even_or_odd N with he | ho
    · right
      refine ⟨even_iff_two_dvd.1 he, fun hU => ?_⟩
      obtain ⟨d, hd, rfl⟩ := hN
      exact hU.2 (2 * d) (by omega) (hF2 d hd).symm
    · exact Or.inl ⟨ho, hN⟩
  have hEU : evenU ⊆ evens := fun N hN => even_iff_two_dvd.1 hN.1
  have c1 : (cnt (Frange 2) X : ℝ) ≤ cnt oddF2 X + cnt (evens \ evenU) X := by
    exact_mod_cast cnt_le_cnt_add_of_subset_union hsub X
  have c2 : (cnt (evens \ evenU) X : ℝ) + cnt evenU X ≤ cnt evens X := by
    exact_mod_cast cnt_sdiff_add_le hEU X
  have c3 : (cnt evens X : ℝ) ≤ X / 2 := by
    have := cnt_dvd_le 2 (by linarith : (0 : ℝ) ≤ X)
    exact_mod_cast this
  have c4 : (cnt oddF2 X : ℝ) ≤ C * Real.sqrt X := hC X hX2
  have c5 : (0.0602757 - ε / 2) * X ≤ (cnt evenU X : ℝ) := h1 X hX1
  have hs0 : 0 ≤ Real.sqrt X := Real.sqrt_nonneg X
  have hss : Real.sqrt X * Real.sqrt X = X := Real.mul_self_sqrt (by linarith)
  have ha : max C 0 / (ε / 2) ≤ Real.sqrt X := Real.le_sqrt_of_sq_le hX3
  have hsq : C * Real.sqrt X ≤ ε / 2 * X := by
    calc C * Real.sqrt X ≤ max C 0 * Real.sqrt X :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hs0
      _ = max C 0 / (ε / 2) * (ε / 2) * Real.sqrt X := by
          rw [div_mul_cancel₀ _ hδ.ne']
      _ ≤ Real.sqrt X * (ε / 2) * Real.sqrt X := by gcongr
      _ = ε / 2 * (Real.sqrt X * Real.sqrt X) := by ring
      _ = ε / 2 * X := by rw [hss]
  linarith

/-- `prop:theta-two` (EP1054.tex lines 2569–2620). -/
theorem link_Prop_ThetaTwo : Principia.Erdos1054.Spine.Link_Prop_ThetaTwo := by
  intro hcount
  refine ⟨?_, by norm_num⟩
  show upperDens (Frange 2) ≤ 1 / 2 - 0.0602757
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨X₀, h⟩ := hcount ε hε
  exact upperDens_le_of_forall_ge (X₀ := X₀) fun X hX => by
    have := h X hX
    linarith

/-- `upperdens(G₂) ≤ θ₂` (EP1054.tex lines 2635–2636). -/
theorem link_Coverage_Step_UpperDensG2 :
    Principia.Erdos1054.Spine.Link_Coverage_Step_UpperDensG2 := by
  intro hdec hsig
  show upperDens (Gcov 2) ≤ upperDens (Frange 2)
  rw [hdec, Set.union_comm, upperDens_union_of_densZero _ hsig]

/-- The `η₂` corollary (EP1054.tex lines 2623–2645). -/
theorem link_Cor_EtaTwo : Principia.Erdos1054.Spine.Link_Cor_EtaTwo := by
  intro hBCC hP2 hG2 hθ
  have h1 := hBCC 2 (by norm_num)
  rw [hP2.2.2.2] at h1
  have h2 := lowerDens_le_upperDens (Gcov 2)
  have h3 : upperDens (Gcov 2) ≤ Coverage.theta2 := hG2
  have h4 := hθ.1
  refine ⟨by linarith, by norm_num⟩

/-- Tail ≤ complement (EP1054.tex lines 2689–2700). -/
theorem link_Coverage_Disp_TailLeCompl :
    Principia.Erdos1054.Spine.Link_Coverage_Disp_TailLeCompl := by
  intro hRc E _hE
  have hU0 : 0 ≤ upperDens {N : ℕ | N ∉ Gcov E} := upperDens_nonneg _
  refine ENNReal.le_of_forall_pos_le_add fun δ hδ _ => ?_
  have hδ' : (0 : ℝ) < δ := hδ
  rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_add hU0 δ.coe_nonneg]
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 (eventually_cnt_lt_mul_of_upperDens_lt
    (show upperDens {N : ℕ | N ∉ Gcov E} < upperDens {N : ℕ | N ∉ Gcov E} + δ / 2 by linarith))
  refine limsup_le_of_le (h := ?_)
  filter_upwards [eventually_ge_atTop
    (max 5 (max (n₀ : ℝ) (4 * (upperDens {N : ℕ | N ∉ Gcov E} + δ) / δ + 1)))] with X hX
  have hX5 : (5 : ℝ) ≤ X := le_trans (le_max_left _ _) hX
  have hXn₀ : (n₀ : ℝ) ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hX
  have hXb : 4 * (upperDens {N : ℕ | N ∉ Gcov E} + δ) / δ + 1 ≤ X :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hX
  have hn5 : 5 ≤ ⌊X⌋₊ := Nat.le_floor (by exact_mod_cast hX5)
  have hnn₀ : n₀ ≤ ⌊X⌋₊ := Nat.le_floor hXn₀
  have hXlt : X < (⌊X⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one X
  have hc : (cnt {N : ℕ | N ∉ Gcov E} X : ℝ) <
      (upperDens {N : ℕ | N ∉ Gcov E} + δ / 2) * (⌊X⌋₊ : ℝ) := by
    have := hn₀ ⌊X⌋₊ hnn₀
    rwa [cnt_floor] at this
  have h4 : 4 * (upperDens {N : ℕ | N ∉ Gcov E} + δ) < δ * (⌊X⌋₊ : ℝ) := by
    have h5 : 4 * (upperDens {N : ℕ | N ∉ Gcov E} + δ) / δ < (⌊X⌋₊ : ℝ) := by linarith
    rw [div_lt_iff₀ hδ'] at h5
    linarith
  refine (nuX_Ioi_le E X).trans ?_
  rw [hRc X hX5]
  apply inv_mul_natCast_le_ofReal (by omega)
  have hcast : ((⌊X⌋₊ - 2 : ℕ) : ℝ) = (⌊X⌋₊ : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega), Nat.cast_ofNat]
  rw [hcast]
  nlinarith

/-- Complement ≤ tail + large cofactors (EP1054.tex lines 2706–2713). -/
theorem link_Coverage_Disp_ComplLeTail :
    Principia.Erdos1054.Spine.Link_Coverage_Disp_ComplLeTail := by
  intro hMom hExact k hk
  obtain ⟨Ck, -, -, hLC⟩ := hMom k hk
  refine ⟨Ck, fun T hT E hE => ?_⟩
  have hE' : (1 : ℝ) ≤ E := by exact_mod_cast hE
  have hsub : {N : ℕ | N ∉ Gcov E} ⊆
      (largeRatioSet T ∪ largeCofactorSet T E) ∪ ({0, 2, 5} : Set ℕ) := by
    intro N hN
    by_cases hR : N ∈ R
    · left
      by_cases hlt : T * N < (f N : ℝ)
      · exact Or.inl ⟨hR, hlt⟩
      · right
        obtain ⟨e, d, he, hd, hfN, hNF⟩ := f_mem_Fform N hR
        refine ⟨e, d, he, hd, hNF, ?_, ?_⟩
        · by_contra hle
          have hle' : e ≤ E := by exact_mod_cast not_lt.1 hle
          exact hN ⟨e, d, he, hle', hd, hNF⟩
        · have h := not_lt.1 hlt
          rw [hfN] at h
          push_cast at h
          exact h
    · right
      rw [hExact] at hR
      have hR' : ¬ (1 ≤ N ∧ N ≠ 2 ∧ N ≠ 5) := hR
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      omega
  have hB : upperDens (largeCofactorSet T E) ≤ Ck * T ^ (k + 1) * (E : ℝ) ^ (1 - (k : ℝ)) :=
    upperDens_le_of_forall_ge (X₀ := 1) fun X hX => hLC T X E hT hX hE'
  have h1 : upperDens {N : ℕ | N ∉ Gcov E} ≤
      upperDens (largeRatioSet T) + Ck * T ^ (k + 1) * (E : ℝ) ^ (1 - (k : ℝ)) := by
    calc upperDens {N : ℕ | N ∉ Gcov E}
        ≤ upperDens ((largeRatioSet T ∪ largeCofactorSet T E) ∪ ({0, 2, 5} : Set ℕ)) :=
          upperDens_mono hsub
      _ = upperDens (largeRatioSet T ∪ largeCofactorSet T E) :=
          upperDens_union_of_densZero _ (densZero_of_finite (Set.toFinite _))
      _ ≤ upperDens (largeRatioSet T) + upperDens (largeCofactorSet T E) :=
          upperDens_union_le _ _
      _ ≤ upperDens (largeRatioSet T) + Ck * T ^ (k + 1) * (E : ℝ) ^ (1 - (k : ℝ)) := by
          linarith
  have h2 : ENNReal.ofReal (upperDens (largeRatioSet T)) ≤
      limsup (fun X : ℝ => nuX X (Set.Ioi (ENNReal.ofReal T))) atTop := by
    refine ENNReal.le_of_forall_pos_le_add fun δ hδ _ => ?_
    have hδ' : (0 : ℝ) < δ := hδ
    have hfreq : ∃ᶠ n : ℕ in atTop,
        upperDens (largeRatioSet T) - δ < (cnt (largeRatioSet T) n : ℝ) / n :=
      frequently_lt_of_lt_limsup (isCoboundedUnder_le_cnt_div _)
        (by show upperDens (largeRatioSet T) - δ < upperDens (largeRatioSet T); linarith)
    have hle : ENNReal.ofReal (upperDens (largeRatioSet T) - δ) ≤
        limsup (fun X : ℝ => nuX X (Set.Ioi (ENNReal.ofReal T))) atTop := by
      apply le_limsup_of_frequently_le'
      rw [Filter.frequently_atTop] at hfreq ⊢
      intro X₀
      obtain ⟨n, hn, hlt⟩ := hfreq (max 1 ⌈X₀⌉₊)
      have hn1 : 1 ≤ n := le_trans (le_max_left _ _) hn
      have hnX : X₀ ≤ (n : ℝ) :=
        le_trans (Nat.le_ceil X₀) (by exact_mod_cast le_trans (le_max_right _ _) hn)
      refine ⟨(n : ℝ), hnX, ?_⟩
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
      have hRle : Rcnt (n : ℝ) ≤ n := by
        have := Rcnt_le_floor (n : ℝ)
        rwa [Nat.floor_natCast] at this
      calc ENNReal.ofReal (upperDens (largeRatioSet T) - δ)
          ≤ ((n : ℝ≥0∞))⁻¹ * (cnt (largeRatioSet T) (n : ℝ) : ℝ≥0∞) :=
            ofReal_le_inv_mul_natCast (by omega) ((lt_div_iff₀ hnpos).1 hlt).le
        _ ≤ ((Rcnt (n : ℝ) : ℝ≥0∞))⁻¹ * (cnt (largeRatioSet T) (n : ℝ) : ℝ≥0∞) :=
            mul_le_mul' (ENNReal.inv_le_inv.2 (by exact_mod_cast hRle)) le_rfl
        _ ≤ nuX (n : ℝ) (Set.Ioi (ENNReal.ofReal T)) := nuX_Ioi_ge T (by linarith) (n : ℝ)
    calc ENNReal.ofReal (upperDens (largeRatioSet T))
        = ENNReal.ofReal ((upperDens (largeRatioSet T) - δ) + δ) := by rw [sub_add_cancel]
      _ ≤ ENNReal.ofReal (upperDens (largeRatioSet T) - δ) + ENNReal.ofReal δ :=
          ENNReal.ofReal_add_le
      _ = ENNReal.ofReal (upperDens (largeRatioSet T) - δ) + δ := by
          rw [ENNReal.ofReal_coe_nnreal]
      _ ≤ limsup (fun X : ℝ => nuX X (Set.Ioi (ENNReal.ofReal T))) atTop + δ :=
          add_le_add hle le_rfl
  calc ENNReal.ofReal (upperDens {N : ℕ | N ∉ Gcov E})
      ≤ ENNReal.ofReal (upperDens (largeRatioSet T) +
          Ck * T ^ (k + 1) * (E : ℝ) ^ (1 - (k : ℝ))) := ENNReal.ofReal_le_ofReal h1
    _ ≤ ENNReal.ofReal (upperDens (largeRatioSet T)) +
          ENNReal.ofReal (Ck * T ^ (k + 1) * (E : ℝ) ^ (1 - (k : ℝ))) := ENNReal.ofReal_add_le
    _ ≤ limsup (fun X : ℝ => nuX X (Set.Ioi (ENNReal.ofReal T))) atTop +
          ENNReal.ofReal (Ck * T ^ (k + 1) * (E : ℝ) ^ (1 - (k : ℝ))) := add_le_add h2 le_rfl

/-- `prop:tightness-equivalence` (EP1054.tex lines 2674–2717). -/
theorem link_Prop_TightnessEquivalence :
    Principia.Erdos1054.Spine.Link_Prop_TightnessEquivalence := by
  intro hTLC hCLT hcompl
  have hfun : (fun E : ℕ => upperDens {N : ℕ | N ∉ Gcov E}) =
      fun E : ℕ => 1 - lowerDens (Gcov E) := funext fun E => hcompl (Gcov E)
  have hii : Eq_TightnessCriterion ↔
      Tendsto (fun E : ℕ => lowerDens (Gcov E)) atTop (𝓝 1) := by
    show Tendsto (fun E : ℕ => upperDens {N : ℕ | N ∉ Gcov E}) atTop (𝓝 0) ↔ _
    rw [hfun]
    constructor
    · intro h
      have h' := (tendsto_const_nhds (x := (1 : ℝ))).sub h
      simp only [sub_sub_cancel, sub_zero] at h'
      exact h'
    · intro h
      have h' := (tendsto_const_nhds (x := (1 : ℝ))).sub h
      rw [sub_self] at h'
      exact h'
  have hi : Coverage.NuTight ↔ Eq_TightnessCriterion :=
    ⟨criterion_of_nuTight hCLT, nuTight_of_criterion hTLC⟩
  exact ⟨hi, hii, hii.symm.trans hi.symm⟩

end Principia.Erdos1054.Proofs
