/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Erdos1054.Spine
import Principia.Erdos1054.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.BigOperators.Ring.Finset

set_option autoImplicit false

/-!
# EP1054 §3: odd representability and the balanced ternary Goldbach reduction

Proves three links of `Principia.Erdos1054.Spine`:

* `link_Lem_AnalyticOddRepresentability_Bound` (`lem:analytic-odd-representability`, paper
  lines 651–670): `Cite_MV_exceptional → Lem_AnalyticOddRepresentability_Bound`. An odd
  `n ∉ 𝓡` has `n ≥ 3` (`1 ∈ 𝓡`), and `n − 1` is either in the Montgomery–Vaughan exceptional set
  or of the form `2p` (a representation `p + q` with `p ≠ q` gives `n = 1 + p + q = F p q ∈ 𝓡`,
  since the divisors of `pq` below `q` are `1, p, q`). The `2p` are counted by
  `π(X) ≤ 8 X / log X` (Mathlib `Chebyshev.pi_le_log4_mul_div`). Constants: the MV exponent `c`,
  implied constant `max C 8`.
* `link_Lem_AnalyticOddRepresentability_LittleO` (line 658): the main bound implies
  `o(X / log log log X)`, via `log₃ X = o(log X)` and `log₃ X = o(X^c)`.
* `link_Lem_FraitureBalancedGoldbach` (`lem:fraiture-balanced-goldbach`, proof lines 856–898):
  `Cite_Helfgott_weighted → Cite_RosserSchoenfeld_psi → Lem_FraitureBalancedGoldbach`. If no
  good triple existed, every weighted term would be dominated (`pointwise`) by one of four
  exceptional classes: a coordinate `p ≤ z`, `q ≤ z` or `r ≤ z` (each of total weight
  `≤ W log H · θ(z) θ(H)`), or a repeated coordinate (at most three `q` per `p`, total
  `≤ 3 W H (log H)³`). With `θ ≤ ψ ≤ 1.03883 t` and `z log H = H/30000` the first three give
  `3 W 1.03883² H²/30000 < 0.000178 H²`; `(log H)³ ≤ 63³ H / e^{62}` for `H ≥ 10^27`
  (`log_cube_le`) makes the fourth `< 3·10⁻²¹ H²`; together they are `< 0.000422 H²`,
  contradicting Helfgott's lower bound. The paper's `10⁻²⁰` is replaced by this sharper
  explicit bound; the inequality chain is otherwise the paper's.

`Lem_AnalyticOddRepresentability` itself is the conjunction the spine assembles by `And.intro`
(no `Link_`), so no theorem is stated for it here.
-/

namespace Principia.Erdos1054.Proofs.OddRepr

open Finset Filter Asymptotics
open Principia.Erdos1054

/-! ## 1. `1 + p + q ∈ 𝓡` for distinct primes -/

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

theorem one_add_add_mem_R {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    1 + p + q ∈ R := by
  rw [mem_R_iff_exists_F]
  rcases lt_or_gt_of_ne hpq with h | h
  · exact ⟨p, q, hp.one_lt.le, hq.one_lt.le, (F_primes hp hq h).symm⟩
  · refine ⟨q, p, hq.one_lt.le, hp.one_lt.le, ?_⟩
    rw [F_primes hq hp h]; ring

theorem one_mem_R : 1 ∈ R := by
  rw [mem_R_iff_exists_F]
  exact ⟨1, 1, le_rfl, le_rfl, by decide⟩

/-! ## 2. Counting the odd exceptions -/

/-- The Montgomery–Vaughan exceptional set: even integers that are not a sum of two primes. -/
def mvSet : Set ℕ := {n : ℕ | Even n ∧ ¬ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p + q}

theorem cnt_oddUnrep_le (X : ℝ) :
    cnt oddUnrep X ≤ cnt mvSet X + Nat.primeCounting ⌊X⌋₊ := by
  classical
  have hmaps : ∀ n ∈ (Icc 1 ⌊X⌋₊).filter (· ∈ oddUnrep),
      n - 1 ∈ ((Icc 1 ⌊X⌋₊).filter (· ∈ mvSet)) ∪ (Nat.primesLE ⌊X⌋₊).image (2 * ·) := by
    intro n hn
    rw [mem_filter, mem_Icc] at hn
    obtain ⟨⟨hn1, hnX⟩, hodd, hnR⟩ := hn
    have hn3 : 3 ≤ n := by
      obtain ⟨k, rfl⟩ := hodd
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · exact absurd one_mem_R hnR
      · omega
    rw [mem_union, mem_filter, mem_Icc, mem_image]
    by_cases hgold : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n - 1 = p + q
    · right
      obtain ⟨p, q, hp, hq, hpq⟩ := hgold
      by_cases hne : p = q
      · subst hne
        exact ⟨p, Nat.mem_primesLE.mpr ⟨by omega, hp⟩, by omega⟩
      · exfalso
        apply hnR
        have hn' : n = 1 + p + q := by omega
        rw [hn']
        exact one_add_add_mem_R hp hq hne
    · left
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      show Even (n - 1) ∧ ¬ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n - 1 = p + q
      obtain ⟨k, hk⟩ := hodd
      exact ⟨⟨k, by omega⟩, hgold⟩
  have hinj : ((Icc 1 ⌊X⌋₊).filter (· ∈ oddUnrep) : Set ℕ).InjOn (fun n => n - 1) := by
    intro a ha b hb hab
    simp only [coe_filter, mem_Icc, Set.mem_setOf_eq] at ha hb
    simp only at hab
    omega
  calc cnt oddUnrep X = ((Icc 1 ⌊X⌋₊).filter (· ∈ oddUnrep)).card := rfl
    _ ≤ (((Icc 1 ⌊X⌋₊).filter (· ∈ mvSet)) ∪ (Nat.primesLE ⌊X⌋₊).image (2 * ·)).card :=
        card_le_card_of_injOn (fun n => n - 1) hmaps hinj
    _ ≤ ((Icc 1 ⌊X⌋₊).filter (· ∈ mvSet)).card + ((Nat.primesLE ⌊X⌋₊).image (2 * ·)).card :=
        card_union_le _ _
    _ ≤ ((Icc 1 ⌊X⌋₊).filter (· ∈ mvSet)).card + (Nat.primesLE ⌊X⌋₊).card :=
        Nat.add_le_add_left card_image_le _
    _ = cnt mvSet X + Nat.primeCounting ⌊X⌋₊ := by
        rw [Nat.primesLE_card_eq_primeCounting]; rfl

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

/-- `log₃ X = log log log X` (definitional). -/
theorem logIt_three (X : ℝ) : logIt 3 X = Real.log (Real.log (Real.log X)) := rfl

/-! ## 3. The balanced ternary Goldbach reduction -/

/-- The product bound `W = ‖η₊‖∞² ‖η_*‖∞` of the paper (line 877). -/
noncomputable def Wc : ℝ := 1.079955 * 1.079955 * 1.414

theorem Wc_nonneg : 0 ≤ Wc := by unfold Wc; norm_num

/-- `lp n = log n` on primes, `0` elsewhere (the summand of `θ`). -/
noncomputable def lp (n : ℕ) : ℝ := if n.Prime then Real.log n else 0

theorem lp_nonneg (n : ℕ) : 0 ≤ lp n := by
  unfold lp
  split_ifs with h
  · exact Real.log_nonneg (by exact_mod_cast h.one_lt.le)
  · exact le_rfl

theorem lp_of_prime {n : ℕ} (h : n.Prime) : lp n = Real.log n := by
  unfold lp; rw [if_pos h]

/-- `lp` restricted to `n ≤ z`. -/
noncomputable def lpLe (z : ℝ) (n : ℕ) : ℝ := if (n : ℝ) ≤ z then lp n else 0

theorem lpLe_nonneg (z : ℝ) (n : ℕ) : 0 ≤ lpLe z n := by
  unfold lpLe; split_ifs
  · exact lp_nonneg n
  · exact le_rfl

/-- The third coordinate `r = H - p - q`, weighted by `lp`, when `r ≤ z`. -/
noncomputable def lpTail (H p : ℕ) (z : ℝ) (q : ℕ) : ℝ :=
  if p + q < H ∧ ((H - p - q : ℕ) : ℝ) ≤ z then lp (H - p - q) else 0

theorem lpTail_nonneg (H p : ℕ) (z : ℝ) (q : ℕ) : 0 ≤ lpTail H p z q := by
  unfold lpTail; split_ifs
  · exact lp_nonneg _
  · exact le_rfl

/-- Indicator of a repeated coordinate in `(p, q, H - p - q)`. -/
noncomputable def rep (H p q : ℕ) : ℝ :=
  if p + q < H ∧ (q = p ∨ H - p - q = p ∨ q = H - p - q) then 1 else 0

theorem rep_nonneg (H p q : ℕ) : 0 ≤ rep H p q := by
  unfold rep; split_ifs
  · exact zero_le_one
  · exact le_rfl

theorem sum_lp_le_theta (s : Finset ℕ) (y : ℝ) (hs : ∀ n ∈ s, (n : ℝ) ≤ y) :
    ∑ n ∈ s, lp n ≤ Chebyshev.theta y := by
  calc ∑ n ∈ s, lp n ≤ ∑ n ∈ range (⌊y⌋₊ + 1), lp n := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro n hn
          rw [Finset.mem_range, Nat.lt_succ_iff]
          exact Nat.le_floor (hs n hn)
        · intro n _ _
          exact lp_nonneg n
    _ = Chebyshev.theta y := by
        rw [Chebyshev.theta_eq_sum_primesLE, Nat.primesLE_eq_filter_range, Finset.sum_filter]
        rfl

theorem sum_lp_range_le (H : ℕ) : ∑ q ∈ range H, lp q ≤ Chebyshev.theta H :=
  sum_lp_le_theta _ _ (fun n hn => by
    have := Finset.mem_range.mp hn
    exact_mod_cast this.le)

theorem sum_lpLe_le (H : ℕ) (z : ℝ) : ∑ p ∈ range H, lpLe z p ≤ Chebyshev.theta z := by
  classical
  unfold lpLe
  rw [← Finset.sum_filter]
  exact sum_lp_le_theta _ z (fun n hn => (Finset.mem_filter.mp hn).2)

theorem sum_lpLe_nonneg (H : ℕ) (z : ℝ) : 0 ≤ ∑ p ∈ range H, lpLe z p :=
  Finset.sum_nonneg (fun p _ => lpLe_nonneg z p)

theorem sum_lp_nonneg (H : ℕ) : 0 ≤ ∑ p ∈ range H, lp p :=
  Finset.sum_nonneg (fun p _ => lp_nonneg p)

theorem sum_lpTail_le (H p : ℕ) (z : ℝ) : ∑ q ∈ range H, lpTail H p z q ≤ Chebyshev.theta z := by
  classical
  unfold lpTail
  rw [← Finset.sum_filter]
  set s := (range H).filter (fun q => p + q < H ∧ ((H - p - q : ℕ) : ℝ) ≤ z) with hs
  have hinj : Set.InjOn (fun q => H - p - q) (s : Set ℕ) := by
    intro a ha b hb hab
    simp only [hs, coe_filter, mem_range, Set.mem_setOf_eq] at ha hb
    simp only at hab
    omega
  calc ∑ q ∈ s, lp (H - p - q) = ∑ r ∈ s.image (fun q => H - p - q), lp r :=
        (Finset.sum_image hinj).symm
    _ ≤ Chebyshev.theta z := by
        apply sum_lp_le_theta
        intro r hr
        rw [Finset.mem_image] at hr
        obtain ⟨q, hq, rfl⟩ := hr
        rw [hs, Finset.mem_filter] at hq
        exact hq.2.2

theorem sum_rep_le (H p : ℕ) : ∑ q ∈ range H, rep H p q ≤ 3 := by
  classical
  unfold rep
  rw [Finset.sum_boole]
  have hsub : (range H).filter (fun q => p + q < H ∧ (q = p ∨ H - p - q = p ∨ q = H - p - q)) ⊆
      {p, H - 2 * p, (H - p) / 2} := by
    intro q hq
    simp only [mem_filter, mem_range] at hq
    simp only [mem_insert, mem_singleton]
    omega
  have := (card_le_card hsub).trans card_le_three
  exact_mod_cast this

theorem double_sum_mul (s : Finset ℕ) (k : ℝ) (f g : ℕ → ℝ) :
    ∑ p ∈ s, ∑ q ∈ s, k * (f p * g q) = k * ((∑ p ∈ s, f p) * (∑ q ∈ s, g q)) := by
  rw [Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.mul_sum]

theorem weight_le (a b c u v w : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hu : |u| ≤ 1.079955) (hv : |v| ≤ 1.079955) (hw : |w| ≤ 1.414) :
    a * b * c * u * v * w ≤ Wc * (a * b * c) := by
  have habc : 0 ≤ a * b * c := by positivity
  have huvw : |u * v * w| ≤ Wc := by
    rw [abs_mul, abs_mul]
    unfold Wc
    exact mul_le_mul (mul_le_mul hu hv (abs_nonneg _) (by norm_num)) hw (abs_nonneg _)
      (by norm_num)
  calc a * b * c * u * v * w = (a * b * c) * (u * v * w) := by ring
    _ ≤ (a * b * c) * |u * v * w| := mul_le_mul_of_nonneg_left (le_abs_self _) habc
    _ ≤ (a * b * c) * Wc := mul_le_mul_of_nonneg_left huvw habc
    _ = Wc * (a * b * c) := by ring

/-- The pointwise domination of one weighted term by the four exceptional classes. -/
theorem pointwise (H p q : ℕ) (z T : ℝ)
    (hpq : p + q < H) (hp : p.Prime) (hq : q.Prime) (hr : (H - p - q).Prime)
    (hT : T ≤ Wc * (Real.log p * Real.log q * Real.log ((H - p - q : ℕ) : ℝ)))
    (hbad : (p : ℝ) ≤ z ∨ (q : ℝ) ≤ z ∨ ((H - p - q : ℕ) : ℝ) ≤ z ∨ q = p ∨ H - p - q = p ∨
      q = H - p - q) :
    T ≤ Wc * Real.log H * (lpLe z p * lp q) + Wc * Real.log H * (lp p * lpLe z q) +
      Wc * Real.log H * (lp p * lpTail H p z q) + Wc * Real.log H ^ 3 * rep H p q := by
  set L := Real.log (H : ℝ) with hL
  have hlog_le : ∀ n : ℕ, 0 < n → n ≤ H → Real.log n ≤ L := fun n hn hnH =>
    Real.log_le_log (by exact_mod_cast hn) (by exact_mod_cast hnH)
  have hlog_nn : ∀ n : ℕ, n.Prime → 0 ≤ Real.log n := fun n hn =>
    Real.log_nonneg (by exact_mod_cast hn.one_lt.le)
  set a := Real.log (p : ℝ) with ha
  set b := Real.log (q : ℝ) with hb
  set c := Real.log ((H - p - q : ℕ) : ℝ) with hc
  have ha0 : 0 ≤ a := hlog_nn p hp
  have hb0 : 0 ≤ b := hlog_nn q hq
  have hc0 : 0 ≤ c := hlog_nn _ hr
  have haL : a ≤ L := hlog_le p hp.pos (by omega)
  have hbL : b ≤ L := hlog_le q hq.pos (by omega)
  have hcL : c ≤ L := hlog_le _ hr.pos (by omega)
  have hL0 : 0 ≤ L := le_trans ha0 haL
  have hW := Wc_nonneg
  have hlpp : lp p = a := lp_of_prime hp
  have hlpq : lp q = b := lp_of_prime hq
  have hlpr : lp (H - p - q) = c := lp_of_prime hr
  have t1 : 0 ≤ Wc * L * (lpLe z p * lp q) :=
    mul_nonneg (mul_nonneg hW hL0) (mul_nonneg (lpLe_nonneg z p) (lp_nonneg q))
  have t2 : 0 ≤ Wc * L * (lp p * lpLe z q) :=
    mul_nonneg (mul_nonneg hW hL0) (mul_nonneg (lp_nonneg p) (lpLe_nonneg z q))
  have t3 : 0 ≤ Wc * L * (lp p * lpTail H p z q) :=
    mul_nonneg (mul_nonneg hW hL0) (mul_nonneg (lp_nonneg p) (lpTail_nonneg H p z q))
  have t4 : 0 ≤ Wc * L ^ 3 * rep H p q :=
    mul_nonneg (mul_nonneg hW (pow_nonneg hL0 3)) (rep_nonneg H p q)
  rcases hbad with h | h | h | h | h | h
  · have hle : lpLe z p = a := by unfold lpLe; rw [if_pos h, hlpp]
    have key : Wc * (a * b * c) ≤ Wc * L * (lpLe z p * lp q) := by
      rw [hle, hlpq]
      have : a * b * c ≤ a * b * L := mul_le_mul_of_nonneg_left hcL (mul_nonneg ha0 hb0)
      calc Wc * (a * b * c) ≤ Wc * (a * b * L) := mul_le_mul_of_nonneg_left this hW
        _ = Wc * L * (a * b) := by ring
    linarith
  · have hle : lpLe z q = b := by unfold lpLe; rw [if_pos h, hlpq]
    have key : Wc * (a * b * c) ≤ Wc * L * (lp p * lpLe z q) := by
      rw [hle, hlpp]
      have : a * b * c ≤ a * b * L := mul_le_mul_of_nonneg_left hcL (mul_nonneg ha0 hb0)
      calc Wc * (a * b * c) ≤ Wc * (a * b * L) := mul_le_mul_of_nonneg_left this hW
        _ = Wc * L * (a * b) := by ring
    linarith
  · have hle : lpTail H p z q = c := by unfold lpTail; rw [if_pos ⟨hpq, h⟩, hlpr]
    have key : Wc * (a * b * c) ≤ Wc * L * (lp p * lpTail H p z q) := by
      rw [hle, hlpp]
      have : a * b * c ≤ a * L * c :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbL ha0) hc0
      calc Wc * (a * b * c) ≤ Wc * (a * L * c) := mul_le_mul_of_nonneg_left this hW
        _ = Wc * L * (a * c) := by ring
    linarith
  all_goals
    have hrep : rep H p q = 1 := by
      unfold rep; rw [if_pos ⟨hpq, by tauto⟩]
    have habc : a * b * c ≤ L ^ 3 := by
      have hab : a * b ≤ L * L := mul_le_mul haL hbL hb0 hL0
      calc a * b * c ≤ L * L * L := mul_le_mul hab hcL hc0 (mul_nonneg hL0 hL0)
        _ = L ^ 3 := by ring
    have key : Wc * (a * b * c) ≤ Wc * L ^ 3 * rep H p q := by
      rw [hrep, mul_one]
      exact mul_le_mul_of_nonneg_left habc hW
    linarith

theorem exp62_eq : Real.exp 62 = Real.exp 1 ^ 62 := by
  rw [← Real.exp_nat_mul]; norm_num

theorem exp62_lower : (5 : ℝ) * 10 ^ 26 ≤ Real.exp 62 := by
  rw [exp62_eq]
  have h1 : (2.718 : ℝ) ≤ Real.exp 1 := le_trans (by norm_num) Real.exp_one_gt_d9.le
  calc (5 : ℝ) * 10 ^ 26 ≤ 2.718 ^ 62 := by norm_num
    _ ≤ Real.exp 1 ^ 62 := pow_le_pow_left₀ (by norm_num) h1 62

theorem exp62_upper : Real.exp 62 < 10 ^ 27 := by
  rw [exp62_eq]
  have h1 : Real.exp 1 < 2.72 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  calc Real.exp 1 ^ 62 < 2.72 ^ 62 :=
        pow_lt_pow_left₀ h1 (Real.exp_pos 1).le (by norm_num)
    _ < 10 ^ 27 := by norm_num

/-- `(log H)³ ≤ 63³ H / e^{62}` for `H ≥ 10^27` (so `3 W H (log H)³ < 10^{-20} H²`). -/
theorem log_cube_le (H : ℝ) (hH : 10 ^ 27 ≤ H) :
    Real.log H ^ 3 * (5 * 10 ^ 26) ≤ 250047 * H := by
  have hHpos : 0 < H := lt_of_lt_of_le (by norm_num) hH
  set L := Real.log H with hL
  have hL62 : 62 < L := by
    rw [hL, Real.lt_log_iff_exp_lt hHpos]
    linarith [exp62_upper]
  set u := L - 62 with hu
  have hu0 : 0 ≤ u := by linarith
  have hexpu : (1 + u / 3) ^ 3 ≤ Real.exp u := by
    have h1 : 1 + u / 3 ≤ Real.exp (u / 3) := by linarith [Real.add_one_le_exp (u / 3)]
    have h2 : Real.exp u = Real.exp (u / 3) ^ 3 := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [h2]
    exact pow_le_pow_left₀ (by linarith) h1 3
  have hHexp : H = Real.exp 62 * Real.exp u := by
    rw [← Real.exp_add, show (62 : ℝ) + u = L by rw [hu]; ring, hL, Real.exp_log hHpos]
  have hLle : L ≤ 63 * (1 + u / 3) := by linarith
  have hL3 : L ^ 3 ≤ (63 * (1 + u / 3)) ^ 3 := pow_le_pow_left₀ (by linarith) hLle 3
  have h62 := exp62_lower
  have hpos : 0 ≤ (63 * (1 + u / 3)) ^ 3 := by positivity
  calc L ^ 3 * (5 * 10 ^ 26) ≤ (63 * (1 + u / 3)) ^ 3 * Real.exp 62 :=
        mul_le_mul hL3 h62 (by norm_num) hpos
    _ = 63 ^ 3 * (1 + u / 3) ^ 3 * Real.exp 62 := by ring
    _ ≤ 63 ^ 3 * Real.exp u * Real.exp 62 := by gcongr
    _ = 250047 * H := by rw [hHexp]; ring

end Principia.Erdos1054.Proofs.OddRepr

namespace Principia.Erdos1054.Proofs

open Finset Filter Asymptotics
open Principia.Erdos1054 Principia.Erdos1054.Proofs.OddRepr

theorem link_Lem_AnalyticOddRepresentability_Bound :
    Principia.Erdos1054.Spine.Link_Lem_AnalyticOddRepresentability_Bound := by
  intro hMV
  obtain ⟨c, hc, C, hC⟩ := hMV
  refine ⟨c, hc, max C 8, fun X hX => ?_⟩
  have h1 : (cnt mvSet X : ℝ) ≤ C * X ^ (1 - c) := hC X (by linarith)
  have h2 := primeCounting_le X hX
  have h3 : (cnt oddUnrep X : ℝ) ≤ cnt mvSet X + Nat.primeCounting ⌊X⌋₊ := by
    exact_mod_cast cnt_oddUnrep_le X
  have hXpos : 0 < X := by linarith
  have hrpow : 0 ≤ X ^ (1 - c) := Real.rpow_nonneg hXpos.le _
  have hdiv : 0 ≤ X / Real.log X := div_nonneg hXpos.le (Real.log_nonneg (by linarith))
  have hC1 : C * X ^ (1 - c) ≤ max C 8 * X ^ (1 - c) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hrpow
  have hC2 : 8 * (X / Real.log X) ≤ max C 8 * (X / Real.log X) :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) hdiv
  rw [mul_add]
  linarith

theorem link_Lem_AnalyticOddRepresentability_LittleO :
    Principia.Erdos1054.Spine.Link_Lem_AnalyticOddRepresentability_LittleO := by
  intro hB ε hε
  obtain ⟨c, hc, C, hC⟩ := hB
  set C' := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  set δ := ε / (2 * C' + 1) with hδdef
  have hδ : 0 < δ := div_pos hε (by linarith)
  have hδε : 2 * C' * δ ≤ ε := by
    rw [hδdef, ← mul_div_assoc, div_le_iff₀ (by linarith)]
    nlinarith
  have hL2 : (fun x : ℝ => Real.log (Real.log x)) =o[atTop] (fun x => Real.log x) :=
    Real.isLittleO_log_id_atTop.comp_tendsto Real.tendsto_log_atTop
  have hLL : Tendsto (fun x : ℝ => Real.log (Real.log x)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have hL3 : (fun x : ℝ => Real.log (Real.log (Real.log x))) =o[atTop]
      (fun x => Real.log (Real.log x)) :=
    Real.isLittleO_log_id_atTop.comp_tendsto hLL
  have hL31 : (fun x : ℝ => Real.log (Real.log (Real.log x))) =o[atTop] (fun x => Real.log x) :=
    hL3.trans hL2
  have hL3c : (fun x : ℝ => Real.log (Real.log (Real.log x))) =o[atTop] (fun x => x ^ c) :=
    hL31.trans (isLittleO_log_rpow_atTop hc)
  have hLLL : Tendsto (fun x : ℝ => Real.log (Real.log (Real.log x))) atTop atTop :=
    Real.tendsto_log_atTop.comp hLL
  have e1 := hL31.bound hδ
  have e2 := hL3c.bound hδ
  have e3 := hLLL.eventually_gt_atTop 0
  have e4 := eventually_ge_atTop (3 : ℝ)
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp (e1.and (e2.and (e3.and e4)))
  refine ⟨X₀, fun X hX => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hX₀ X hX
  rw [logIt_three]
  have hXpos : 0 < X := by linarith
  have hL1pos : 0 < Real.log X := Real.log_pos (by linarith)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos h3, abs_of_pos hL1pos] at h1
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos h3,
    abs_of_nonneg (Real.rpow_nonneg hXpos.le c)] at h2
  have hBX := hC X h4
  have hrpow : 0 ≤ X ^ (1 - c) := Real.rpow_nonneg hXpos.le _
  have hdiv : 0 ≤ X / Real.log X := div_nonneg hXpos.le hL1pos.le
  have hCC : C * (X ^ (1 - c) + X / Real.log X) ≤ C' * (X ^ (1 - c) + X / Real.log X) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  have hsplit : X ^ (1 - c) * X ^ c = X := by
    rw [← Real.rpow_add hXpos]; simp
  have ha : X ^ (1 - c) ≤ δ * (X / Real.log (Real.log (Real.log X))) := by
    rw [mul_div_assoc', le_div_iff₀ h3]
    calc X ^ (1 - c) * Real.log (Real.log (Real.log X))
        ≤ X ^ (1 - c) * (δ * X ^ c) := mul_le_mul_of_nonneg_left h2 hrpow
      _ = δ * (X ^ (1 - c) * X ^ c) := by ring
      _ = δ * X := by rw [hsplit]
  have hb : X / Real.log X ≤ δ * (X / Real.log (Real.log (Real.log X))) := by
    rw [mul_div_assoc', div_le_div_iff₀ hL1pos h3]
    nlinarith
  have hXL3 : 0 ≤ X / Real.log (Real.log (Real.log X)) := div_nonneg hXpos.le h3.le
  have hfin : C' * (X ^ (1 - c) + X / Real.log X) ≤
      ε * (X / Real.log (Real.log (Real.log X))) := by
    calc C' * (X ^ (1 - c) + X / Real.log X)
        ≤ C' * (δ * (X / Real.log (Real.log (Real.log X))) +
            δ * (X / Real.log (Real.log (Real.log X)))) :=
          mul_le_mul_of_nonneg_left (add_le_add ha hb) hC'0
      _ = (2 * C' * δ) * (X / Real.log (Real.log (Real.log X))) := by ring
      _ ≤ ε * (X / Real.log (Real.log (Real.log X))) :=
          mul_le_mul_of_nonneg_right hδε hXL3
  linarith

theorem link_Lem_FraitureBalancedGoldbach :
    Principia.Erdos1054.Spine.Link_Lem_FraitureBalancedGoldbach := by
  intro hHelf hRS H hHodd hH
  obtain ⟨ηp, ηs, hηp, hηs, hsum⟩ := hHelf H hHodd hH
  by_contra hno
  have hHR : (10 : ℝ) ^ 27 ≤ (H : ℝ) := by exact_mod_cast hH
  have hHpos : (0 : ℝ) < H := lt_of_lt_of_le (by norm_num) hHR
  set L := Real.log (H : ℝ) with hL
  have hL3 := log_cube_le (H : ℝ) hHR
  have hLpos : 0 < L := Real.log_pos (lt_of_lt_of_le (by norm_num) hHR)
  set z := (H : ℝ) / (30000 * L) with hz
  have hzpos : 0 < z := div_pos hHpos (by positivity)
  have hLne : L ≠ 0 := hLpos.ne'
  have hzL : z * L = H / 30000 := by rw [hz]; field_simp
  -- every weighted triple is exceptional
  have hbad : ∀ p q : ℕ, p + q < H → p.Prime → q.Prime → (H - p - q).Prime →
      Odd p → Odd q → Odd (H - p - q) →
      (p : ℝ) ≤ z ∨ (q : ℝ) ≤ z ∨ ((H - p - q : ℕ) : ℝ) ≤ z ∨ q = p ∨ H - p - q = p ∨
        q = H - p - q := by
    intro p q hpq hp hq hr op oq or
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hcon
    exact hno ⟨p, q, H - p - q, hp, hq, hr, op, oq, or, fun h => h4 h.symm,
      fun h => h5 h.symm, h6, by omega, h1, h2, h3⟩
  have hW := Wc_nonneg
  have hWL : 0 ≤ Wc * L := mul_nonneg hW hLpos.le
  have hθz := Chebyshev.theta_nonneg z
  have hθH := Chebyshev.theta_nonneg (H : ℝ)
  have hθz' : Chebyshev.theta z ≤ 1.03883 * z :=
    (Chebyshev.theta_le_psi z).trans (hRS z hzpos)
  have hθH' : Chebyshev.theta (H : ℝ) ≤ 1.03883 * H :=
    (Chebyshev.theta_le_psi _).trans (hRS _ hHpos)
  have hS1 : ∑ p ∈ range H, ∑ q ∈ range H, Wc * L * (lpLe z p * lp q) ≤
      Wc * L * (Chebyshev.theta z * Chebyshev.theta H) := by
    rw [double_sum_mul]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul (sum_lpLe_le H z) (sum_lp_range_le H) (sum_lp_nonneg H) hθz) hWL
  have hS2 : ∑ p ∈ range H, ∑ q ∈ range H, Wc * L * (lp p * lpLe z q) ≤
      Wc * L * (Chebyshev.theta H * Chebyshev.theta z) := by
    rw [double_sum_mul]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul (sum_lp_range_le H) (sum_lpLe_le H z) (sum_lpLe_nonneg H z) hθH) hWL
  have hS3 : ∑ p ∈ range H, ∑ q ∈ range H, Wc * L * (lp p * lpTail H p z q) ≤
      Wc * L * (Chebyshev.theta H * Chebyshev.theta z) := by
    calc ∑ p ∈ range H, ∑ q ∈ range H, Wc * L * (lp p * lpTail H p z q)
        = ∑ p ∈ range H, Wc * L * lp p * ∑ q ∈ range H, lpTail H p z q := by
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun q _ => by ring
      _ ≤ ∑ p ∈ range H, Wc * L * lp p * Chebyshev.theta z :=
          Finset.sum_le_sum fun p _ =>
            mul_le_mul_of_nonneg_left (sum_lpTail_le H p z) (mul_nonneg hWL (lp_nonneg p))
      _ = Wc * L * ((∑ p ∈ range H, lp p) * Chebyshev.theta z) := by
          rw [Finset.sum_mul, Finset.mul_sum]
          exact Finset.sum_congr rfl fun p _ => by ring
      _ ≤ Wc * L * (Chebyshev.theta H * Chebyshev.theta z) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (sum_lp_range_le H) hθz) hWL
  have hS4 : ∑ p ∈ range H, ∑ q ∈ range H, Wc * L ^ 3 * rep H p q ≤
      (H : ℝ) * (Wc * L ^ 3 * 3) := by
    calc ∑ p ∈ range H, ∑ q ∈ range H, Wc * L ^ 3 * rep H p q
        = ∑ p ∈ range H, Wc * L ^ 3 * ∑ q ∈ range H, rep H p q :=
          Finset.sum_congr rfl fun p _ => (Finset.mul_sum _ _ _).symm
      _ ≤ ∑ p ∈ range H, Wc * L ^ 3 * 3 :=
          Finset.sum_le_sum fun p _ =>
            mul_le_mul_of_nonneg_left (sum_rep_le H p) (mul_nonneg hW (pow_nonneg hLpos.le 3))
      _ = (H : ℝ) * (Wc * L ^ 3 * 3) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- the numerics
  have hP1 : Chebyshev.theta z * Chebyshev.theta H ≤ (1.03883 * z) * (1.03883 * H) :=
    mul_le_mul hθz' hθH' hθH (by positivity)
  have hP2 : Wc * L * (Chebyshev.theta z * Chebyshev.theta H) ≤
      Wc * 1.03883 ^ 2 * (H / 30000) * H := by
    calc Wc * L * (Chebyshev.theta z * Chebyshev.theta H)
        ≤ Wc * L * ((1.03883 * z) * (1.03883 * H)) := mul_le_mul_of_nonneg_left hP1 hWL
      _ = Wc * 1.03883 ^ 2 * (z * L) * H := by ring
      _ = Wc * 1.03883 ^ 2 * (H / 30000) * H := by rw [hzL]
  have hP3 : (H : ℝ) * (Wc * L ^ 3 * 3) ≤ (H : ℝ) * (Wc * (250047 * H / (5 * 10 ^ 26)) * 3) := by
    have : L ^ 3 ≤ 250047 * H / (5 * 10 ^ 26) := by
      rw [le_div_iff₀ (by norm_num)]; exact hL3
    have h' : Wc * L ^ 3 * 3 ≤ Wc * (250047 * H / (5 * 10 ^ 26)) * 3 := by
      have := mul_le_mul_of_nonneg_left this hW
      linarith
    exact mul_le_mul_of_nonneg_left h' hHpos.le
  have hcoef : Wc * (3 * 1.03883 ^ 2 / 30000 + 3 * 250047 / (5 * 10 ^ 26)) < 0.000422 := by
    unfold Wc; norm_num
  have hHH : 0 < (H : ℝ) * H := mul_pos hHpos hHpos
  have hfin : Wc * (3 * 1.03883 ^ 2 / 30000 + 3 * 250047 / (5 * 10 ^ 26)) * ((H : ℝ) * H) <
      0.000422 * ((H : ℝ) * H) := mul_lt_mul_of_pos_right hcoef hHH
  have hTH : Chebyshev.theta H * Chebyshev.theta z = Chebyshev.theta z * Chebyshev.theta H :=
    mul_comm _ _
  apply absurd hsum
  rw [not_le]
  calc _ ≤ ∑ p ∈ range H, ∑ q ∈ range H,
        (Wc * L * (lpLe z p * lp q) + Wc * L * (lp p * lpLe z q) +
          Wc * L * (lp p * lpTail H p z q) + Wc * L ^ 3 * rep H p q) := by
        apply Finset.sum_le_sum
        intro p _
        apply Finset.sum_le_sum
        intro q _
        split_ifs with hc
        · obtain ⟨hpq, hp, hq, hr, op, oq, or⟩ := hc
          exact pointwise H p q z _ hpq hp hq hr
            (weight_le _ _ _ _ _ _
              (Real.log_nonneg (by exact_mod_cast hp.one_lt.le))
              (Real.log_nonneg (by exact_mod_cast hq.one_lt.le))
              (Real.log_nonneg (by exact_mod_cast hr.one_lt.le))
              (hηp _) (hηp _) (hηs _))
            (hbad p q hpq hp hq hr op oq or)
        · have t1 : 0 ≤ Wc * L * (lpLe z p * lp q) :=
            mul_nonneg hWL (mul_nonneg (lpLe_nonneg z p) (lp_nonneg q))
          have t2 : 0 ≤ Wc * L * (lp p * lpLe z q) :=
            mul_nonneg hWL (mul_nonneg (lp_nonneg p) (lpLe_nonneg z q))
          have t3 : 0 ≤ Wc * L * (lp p * lpTail H p z q) :=
            mul_nonneg hWL (mul_nonneg (lp_nonneg p) (lpTail_nonneg H p z q))
          have t4 : 0 ≤ Wc * L ^ 3 * rep H p q :=
            mul_nonneg (mul_nonneg hW (pow_nonneg hLpos.le 3)) (rep_nonneg H p q)
          linarith
    _ = ∑ p ∈ range H, ∑ q ∈ range H, Wc * L * (lpLe z p * lp q) +
          ∑ p ∈ range H, ∑ q ∈ range H, Wc * L * (lp p * lpLe z q) +
          ∑ p ∈ range H, ∑ q ∈ range H, Wc * L * (lp p * lpTail H p z q) +
          ∑ p ∈ range H, ∑ q ∈ range H, Wc * L ^ 3 * rep H p q := by
        simp only [Finset.sum_add_distrib]
    _ ≤ Wc * L * (Chebyshev.theta z * Chebyshev.theta H) +
          Wc * L * (Chebyshev.theta H * Chebyshev.theta z) +
          Wc * L * (Chebyshev.theta H * Chebyshev.theta z) +
          (H : ℝ) * (Wc * L ^ 3 * 3) :=
        add_le_add (add_le_add (add_le_add hS1 hS2) hS3) hS4
    _ = 3 * (Wc * L * (Chebyshev.theta z * Chebyshev.theta H)) +
          (H : ℝ) * (Wc * L ^ 3 * 3) := by
        rw [hTH]; ring
    _ ≤ 3 * (Wc * 1.03883 ^ 2 * (H / 30000) * H) +
          (H : ℝ) * (Wc * (250047 * H / (5 * 10 ^ 26)) * 3) := by
        linarith
    _ = Wc * (3 * 1.03883 ^ 2 / 30000 + 3 * 250047 / (5 * 10 ^ 26)) * ((H : ℝ) * H) := by
        ring
    _ < 0.000422 * ((H : ℝ) * H) := hfin
    _ = 0.000422 * (H : ℝ) ^ 2 := by ring

end Principia.Erdos1054.Proofs
