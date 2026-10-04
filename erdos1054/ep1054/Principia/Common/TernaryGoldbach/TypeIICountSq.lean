/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.TernaryGoldbach.TypeIIMonro2B
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues

set_option autoImplicit false

/-!
# `M2B.CountSq` PROVED, hence `M2H.MonroFleming` PROVED

`M2B.CountSq` (`TypeIIMonro2B`): for square-free `k` and `0 ≤ b/2 ≤ a ≤ b`,
`|#{a < l ≤ b : l square-free, (l, k) = 1} − (6/π²)(k/σ(k))(b − a)| ≤ 1.5·∑_{e ∣ k} √(b/e)`.
This is the book's `eq:etze`-`eq:totor` (`minarcs.tex` 2692-2787) for one modulus:

```
 point_id     [(l,k)=1 ∧ l sq-free] = ∑_{e∣k} ∑_{(m,k)=1, em²∣l} μ(e)μ(m)     PROVED
 nSq_expand   # = ∑_{e∣k} ∑_{m≤⌊b⌋, (m,k)=1} μ(e)μ(m)(⌊b⌋/em² − ⌊a⌋/em²)   PROVED
 Ck_one       ∑ μ(m)/m² = 6/π²   (Mathlib: L(ζ,2)L(μ,2) = 1, ζ(2) = π²/6)      PROVED
 Ck_prime     C_{kp}(1 − 1/p²) = C_k for p ∤ k   (C_k = ∑_{(m,k)=1} μ(m)/m²)   PROVED
 main_const   (∑_{e∣k} μ(e)/e)·C_k = (6/π²)k/σ(k)                               PROVED
 tail_gk      |∑_{m>n} g_k(m)| ≤ 1/(n + 1/2)                                    PROVED
 f_bound      ⌊X⌋ + (X²/2)/(⌊X⌋ + 1/2) ≤ 1.5X                                   PROVED
 e_bound      the error of one divisor e is ≤ 1.5√(b/e)                         PROVED
 countSq_holds      : M2B.CountSq                                               PROVED
 monroFleming_holds : M2H.MonroFleming                                          PROVED
```

The only analytic input is Mathlib's (`riemannZeta_two`, `LSeries_zeta_mul_Lseries_moebius`); no
computation, no literature hypothesis. `f(x) ≤ 1.5x` replaces Helfgott's numerically checked
`1.26981x` (not citable: not among `HelfgottCited`), at the cost of the constant `10.25` in
`M2B.Monro2B`, which `M2H.MonroFleming` absorbs (`20.5 ≤ 22.6418`).
-/

namespace Principia.Common.TernaryGoldbach.M2Q

open ArithmeticFunction

/-! ## (1) Möbius inversion of `(l, k) = 1` and of `l` square-free -/

/-- `∑_{d ∣ n} μ(d) = [n = 1]`. -/
theorem sum_mu_divisors (n : ℕ) :
    ∑ d ∈ n.divisors, (moebius d : ℤ) = if n = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f n) moebius_mul_coe_zeta
  rw [coe_mul_zeta_apply, one_apply] at h
  exact h

/-- `∑_{e ∣ k, e ∣ l} μ(e) = [(l, k) = 1]`. -/
theorem sum_mu_coprime (k l : ℕ) (hk : k ≠ 0) :
    ∑ e ∈ k.divisors.filter (· ∣ l), (moebius e : ℤ) = if Nat.Coprime l k then 1 else 0 := by
  have hg : Nat.gcd l k ≠ 0 := Nat.gcd_ne_zero_right hk
  have hset : k.divisors.filter (· ∣ l) = (Nat.gcd l k).divisors := by
    ext e
    simp only [Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
    constructor
    · rintro ⟨⟨h1, -⟩, h2⟩
      exact ⟨⟨h2, h1⟩, hg⟩
    · rintro ⟨⟨h1, h2⟩, -⟩
      exact ⟨⟨h2, hk⟩, h1⟩
  rw [hset, sum_mu_divisors]

/-- `m² ∣ b²a` with `a` square-free forces `m ∣ b`. -/
theorem dvd_of_sq_dvd (m b a : ℕ) (hm : 0 < m) (ha : Squarefree a) (h : m ^ 2 ∣ b ^ 2 * a) :
    m ∣ b := by
  have hg : 0 < Nat.gcd m b := Nat.gcd_pos_of_pos_left _ hm
  obtain ⟨m1, b1, hc, hm1, hb1⟩ := Nat.exists_coprime m b
  set g := Nat.gcd m b
  have h2 : m1 ^ 2 * g ^ 2 ∣ b1 ^ 2 * a * g ^ 2 := by
    have : m1 ^ 2 * g ^ 2 = m ^ 2 := by rw [hm1]; ring
    rw [this]
    have : b1 ^ 2 * a * g ^ 2 = b ^ 2 * a := by rw [hb1]; ring
    rw [this]
    exact h
  have h3 : m1 ^ 2 ∣ b1 ^ 2 * a := Nat.dvd_of_mul_dvd_mul_right (by positivity) h2
  have h4 : m1 ^ 2 ∣ a := (Nat.Coprime.pow 2 2 hc).dvd_of_dvd_mul_left h3
  have h5 : m1 = 1 := Nat.isUnit_iff.mp (ha m1 (by rw [← sq]; exact h4))
  rw [hm1, h5, one_mul]
  exact Nat.gcd_dvd_right m b

/-- `∑_{m ≤ M, m² ∣ l} μ(m) = [l square-free]` for `1 ≤ l ≤ M`. -/
theorem sum_mu_sq (l M : ℕ) (hl : 0 < l) (hM : l ≤ M) :
    ∑ m ∈ (Finset.Icc 1 M).filter (fun m => m ^ 2 ∣ l), (moebius m : ℤ) =
      if Squarefree l then 1 else 0 := by
  obtain ⟨a, b, ha, hb, hab, hsq⟩ := Nat.sq_mul_squarefree_of_pos hl
  have hbl : b ≤ l := by
    rw [← hab]
    calc b ≤ b ^ 2 := by nlinarith
      _ ≤ b ^ 2 * a := Nat.le_mul_of_pos_right _ ha
  have hset : (Finset.Icc 1 M).filter (fun m => m ^ 2 ∣ l) = b.divisors := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨h1, -⟩, h2⟩
      rw [← hab] at h2
      exact ⟨dvd_of_sq_dvd m b a h1 hsq h2, hb.ne'⟩
    · rintro ⟨h1, -⟩
      have hm0 : 0 < m := Nat.pos_of_dvd_of_pos h1 hb
      refine ⟨⟨hm0, (Nat.le_of_dvd hb h1).trans (hbl.trans hM)⟩, ?_⟩
      rw [← hab]
      exact Dvd.dvd.mul_right (pow_dvd_pow_of_dvd h1 2) a
  rw [hset, sum_mu_divisors]
  have hiff : b = 1 ↔ Squarefree l := by
    constructor
    · rintro rfl
      rw [← hab, one_pow, one_mul]
      exact hsq
    · intro hl'
      exact Nat.isUnit_iff.mp (hl' b ⟨a, by rw [← hab]; ring⟩)
  by_cases h : b = 1
  · rw [if_pos h, if_pos (hiff.mp h)]
  · rw [if_neg h, if_neg (fun h' => h (hiff.mpr h'))]

/-- **The pointwise identity**: for `1 ≤ l ≤ M`,
`[(l, k) = 1 ∧ l square-free] = ∑_{e ∣ k} ∑_{m ≤ M, (m, k) = 1, em² ∣ l} μ(e)μ(m)`. -/
theorem point_id (k l M : ℕ) (hk : k ≠ 0) (hl : 0 < l) (hM : l ≤ M) :
    (if Nat.Coprime l k ∧ Squarefree l then (1 : ℤ) else 0) =
      ∑ e ∈ k.divisors, ∑ m ∈ Finset.Icc 1 M,
        if Nat.Coprime m k ∧ e * m ^ 2 ∣ l then (moebius e : ℤ) * moebius m else 0 := by
  rw [Finset.sum_comm]
  have inner : ∀ m ∈ Finset.Icc 1 M, ∑ e ∈ k.divisors,
      (if Nat.Coprime m k ∧ e * m ^ 2 ∣ l then (moebius e : ℤ) * moebius m else 0) =
      if Nat.Coprime m k ∧ m ^ 2 ∣ l then
        (moebius m : ℤ) * (if Nat.Coprime l k then 1 else 0) else 0 := by
    intro m _
    by_cases hmk : Nat.Coprime m k
    · by_cases hm2 : m ^ 2 ∣ l
      · rw [if_pos ⟨hmk, hm2⟩, ← sum_mu_coprime k l hk, Finset.mul_sum, Finset.sum_filter]
        refine Finset.sum_congr rfl fun e he => ?_
        have hek : e ∣ k := Nat.dvd_of_mem_divisors he
        have hcop : Nat.Coprime e (m ^ 2) :=
          Nat.Coprime.pow_right 2 (Nat.Coprime.coprime_dvd_left hek hmk.symm)
        by_cases hel : e ∣ l
        · rw [if_pos ⟨hmk, hcop.mul_dvd_of_dvd_of_dvd hel hm2⟩, if_pos hel]
          ring
        · rw [if_neg (fun h => hel (Nat.dvd_trans (Dvd.intro _ rfl) h.2)), if_neg hel]
      · rw [if_neg (fun h => hm2 h.2)]
        exact Finset.sum_eq_zero fun e _ => if_neg fun h => hm2 (Nat.dvd_trans
          (Dvd.intro_left _ rfl) h.2)
    · rw [if_neg (fun h => hmk h.1)]
      exact Finset.sum_eq_zero fun e _ => if_neg fun h => hmk h.1
  rw [Finset.sum_congr rfl inner]
  by_cases hlk : Nat.Coprime l k
  · have h1 : ∀ m ∈ Finset.Icc 1 M,
        (if Nat.Coprime m k ∧ m ^ 2 ∣ l then
          (moebius m : ℤ) * (if Nat.Coprime l k then 1 else 0) else 0) =
        if m ^ 2 ∣ l then (moebius m : ℤ) else 0 := by
      intro m _
      rw [if_pos hlk, mul_one]
      by_cases hm2 : m ^ 2 ∣ l
      · have hml : m ∣ l := Nat.dvd_trans (Dvd.intro (m ^ 1) (by ring)) hm2
        rw [if_pos ⟨Nat.Coprime.coprime_dvd_left hml hlk, hm2⟩, if_pos hm2]
      · rw [if_neg (fun h => hm2 h.2), if_neg hm2]
    rw [Finset.sum_congr rfl h1, ← Finset.sum_filter, sum_mu_sq l M hl hM]
    by_cases hsq : Squarefree l
    · rw [if_pos ⟨hlk, hsq⟩, if_pos hsq]
    · rw [if_neg (fun h => hsq h.2), if_neg hsq]
  · rw [if_neg (fun h => hlk h.1)]
    refine (Finset.sum_eq_zero fun m _ => ?_).symm
    rw [if_neg hlk, mul_zero, ite_self]

/-- `#{a < l ≤ b : d ∣ l} = ⌊b⌋/d − ⌊a⌋/d`. -/
theorem cnt_eq (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (d : ℕ) :
    ((Finset.Icc 1 ⌊b⌋₊).filter (fun l : ℕ => a < (l : ℝ) ∧ d ∣ l)).card =
      ⌊b⌋₊ / d - ⌊a⌋₊ / d := by
  have hAB : ⌊a⌋₊ ≤ ⌊b⌋₊ := Nat.floor_le_floor hab
  have hset : (Finset.Icc 1 ⌊b⌋₊).filter (fun l : ℕ => a < (l : ℝ) ∧ d ∣ l) =
      (Finset.Ioc ⌊a⌋₊ ⌊b⌋₊).filter (fun l => d ∣ l) := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
    rw [← Nat.floor_lt ha]
    omega
  have hU : (Finset.Ioc 0 ⌊b⌋₊).filter (fun l => d ∣ l) =
      (Finset.Ioc 0 ⌊a⌋₊).filter (fun l => d ∣ l) ∪
        (Finset.Ioc ⌊a⌋₊ ⌊b⌋₊).filter (fun l => d ∣ l) := by
    rw [← Finset.filter_union, Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le _) hAB]
  have hD : Disjoint ((Finset.Ioc 0 ⌊a⌋₊).filter (fun l => d ∣ l))
      ((Finset.Ioc ⌊a⌋₊ ⌊b⌋₊).filter (fun l => d ∣ l)) := by
    rw [Finset.disjoint_left]
    intro l h1 h2
    simp only [Finset.mem_filter, Finset.mem_Ioc] at h1 h2
    omega
  have hc := congrArg Finset.card hU
  rw [Finset.card_union_of_disjoint hD, Nat.Ioc_filter_dvd_card_eq_div,
    Nat.Ioc_filter_dvd_card_eq_div] at hc
  rw [hset]
  omega

/-- **`nSq` expanded**: `# = ∑_{e ∣ k} ∑_{m ≤ ⌊b⌋, (m,k)=1} μ(e)μ(m)(⌊b⌋/em² − ⌊a⌋/em²)`. -/
theorem nSq_expand (k : ℕ) (hk : k ≠ 0) (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    M2B.nSq k a b = ∑ e ∈ k.divisors, ∑ m ∈ Finset.Icc 1 ⌊b⌋₊,
      (if Nat.Coprime m k then ((moebius e : ℤ) : ℝ) * ((moebius m : ℤ) : ℝ) else 0) *
        (((⌊b⌋₊ / (e * m ^ 2) - ⌊a⌋₊ / (e * m ^ 2) : ℕ)) : ℝ) := by
  unfold M2B.nSq
  rw [Finset.card_filter]
  push_cast
  have hpt : ∀ l ∈ Finset.Icc 1 ⌊b⌋₊,
      (if a < (l : ℝ) ∧ Nat.Coprime l k ∧ Squarefree l then (1 : ℝ) else 0) =
        ∑ e ∈ k.divisors, ∑ m ∈ Finset.Icc 1 ⌊b⌋₊,
          if a < (l : ℝ) ∧ Nat.Coprime m k ∧ e * m ^ 2 ∣ l then
            ((moebius e : ℤ) : ℝ) * ((moebius m : ℤ) : ℝ) else 0 := by
    intro l hl
    have hl' := Finset.mem_Icc.mp hl
    by_cases hal : a < (l : ℝ)
    · have h := point_id k l ⌊b⌋₊ hk hl'.1 hl'.2
      have h' := congrArg (fun z : ℤ => (z : ℝ)) h
      simp only [hal, true_and]
      push_cast [apply_ite] at h'
      exact h'
    · simp only [hal, false_and, if_false, Finset.sum_const_zero]
  rw [Finset.sum_congr rfl hpt, Finset.sum_comm]
  refine Finset.sum_congr rfl fun e he => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m hm => ?_
  have he0 : 0 < e := Nat.pos_of_mem_divisors he
  by_cases hmk : Nat.Coprime m k
  · rw [if_pos hmk]
    have hrw : ∀ l ∈ Finset.Icc 1 ⌊b⌋₊,
        (if a < (l : ℝ) ∧ Nat.Coprime m k ∧ e * m ^ 2 ∣ l then
          ((moebius e : ℤ) : ℝ) * ((moebius m : ℤ) : ℝ) else 0) =
        if a < (l : ℝ) ∧ e * m ^ 2 ∣ l then
          ((moebius e : ℤ) : ℝ) * ((moebius m : ℤ) : ℝ) else 0 := by
      intro l _
      exact if_congr ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hmk, h.2⟩⟩ rfl rfl
    rw [Finset.sum_congr rfl hrw, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
      cnt_eq a b ha hab, mul_comm]
  · rw [if_neg hmk, zero_mul]
    exact Finset.sum_eq_zero fun l _ => if_neg fun h => hmk h.2.1

/-! ## (2) `C_k = ∑_{(m,k)=1} μ(m)/m²`: summability, splitting, the tail -/

/-- `g_k(m) = [(m, k) = 1]·μ(m)/m²`. -/
noncomputable def gk (k m : ℕ) : ℝ :=
  if Nat.Coprime m k then ((moebius m : ℤ) : ℝ) / (m : ℝ) ^ 2 else 0

/-- `C_k = ∑_m g_k(m)`. -/
noncomputable def Ck (k : ℕ) : ℝ := ∑' m, gk k m

theorem abs_gk_le (k m : ℕ) : |gk k m| ≤ 1 / (m : ℝ) ^ 2 := by
  unfold gk
  split_ifs
  · rw [abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (m : ℝ) ^ 2)]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    rw [← Int.cast_abs]
    exact_mod_cast abs_moebius_le_one
  · rw [abs_zero]
    positivity

theorem summable_inv_sq : Summable (fun m : ℕ => 1 / (m : ℝ) ^ 2) :=
  Real.summable_one_div_nat_pow.mpr one_lt_two

theorem summable_gk (k : ℕ) : Summable (gk k) :=
  Summable.of_norm_bounded summable_inv_sq fun m => by
    rw [Real.norm_eq_abs]
    exact abs_gk_le k m

theorem gk_zero (k : ℕ) : gk k 0 = 0 := by
  unfold gk
  split_ifs <;> simp

/-- `1/t² ≤ 1/(t − 1/2) − 1/(t + 1/2)` for `t ≥ 1`. -/
theorem inv_sq_le (t : ℝ) (ht : 1 ≤ t) : 1 / t ^ 2 ≤ 1 / (t - 1 / 2) - 1 / (t + 1 / 2) := by
  have h1 : 0 < t - 1 / 2 := by linarith
  have h2 : 0 < t + 1 / 2 := by linarith
  have e : 1 / (t - 1 / 2) - 1 / (t + 1 / 2) = 1 / (t ^ 2 - 1 / 4) := by
    rw [div_sub_div _ _ (ne_of_gt h1) (ne_of_gt h2)]
    congr 1 <;> ring
  rw [e]
  exact one_div_le_one_div_of_le (by nlinarith) (by linarith)

/-- **The tail**: `∑_{j ≥ 0} 1/(j + n + 1)² ≤ 1/(n + 1/2)`. -/
theorem tail_inv_sq (n : ℕ) :
    ∑' j : ℕ, 1 / ((j : ℝ) + n + 1) ^ 2 ≤ 1 / ((n : ℝ) + 1 / 2) := by
  refine Real.tsum_le_of_sum_range_le (fun j => by positivity) fun J => ?_
  have hstep : ∀ j ∈ Finset.range J, 1 / ((j : ℝ) + n + 1) ^ 2 ≤
      1 / ((j : ℝ) + n + 1 / 2) - 1 / (((j + 1 : ℕ) : ℝ) + n + 1 / 2) := by
    intro j _
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have := inv_sq_le ((j : ℝ) + n + 1) (by linarith)
    push_cast
    have e1 : (j : ℝ) + n + 1 - 1 / 2 = j + n + 1 / 2 := by ring
    have e2 : (j : ℝ) + n + 1 + 1 / 2 = (j : ℝ) + 1 + n + 1 / 2 := by ring
    rw [e1, e2] at this
    exact this
  refine (Finset.sum_le_sum hstep).trans ?_
  rw [Finset.sum_range_sub']
  have : 0 ≤ 1 / (((J : ℕ) : ℝ) + n + 1 / 2) := by positivity
  push_cast at this ⊢
  simp only [zero_add]
  linarith

/-- `|∑_{j} g_k(j + n + 1)| ≤ 1/(n + 1/2)`. -/
theorem tail_gk (k n : ℕ) : |∑' j, gk k (j + (n + 1))| ≤ 1 / ((n : ℝ) + 1 / 2) := by
  have hs : Summable (fun j => gk k (j + (n + 1))) :=
    (summable_nat_add_iff (n + 1)).mpr (summable_gk k)
  have hsa : Summable (fun j => |gk k (j + (n + 1))|) := hs.abs
  have hsq : Summable (fun j : ℕ => 1 / ((j : ℝ) + n + 1) ^ 2) := by
    have := (summable_nat_add_iff (n + 1)).mpr summable_inv_sq
    refine this.congr fun j => ?_
    push_cast
    ring_nf
  calc |∑' j, gk k (j + (n + 1))| ≤ ∑' j, |gk k (j + (n + 1))| := by
        have := norm_tsum_le_tsum_norm (f := fun j => gk k (j + (n + 1)))
          (by simpa only [Real.norm_eq_abs] using hsa)
        simpa only [Real.norm_eq_abs] using this
    _ ≤ ∑' j : ℕ, 1 / ((j : ℝ) + n + 1) ^ 2 := by
        refine Summable.tsum_le_tsum (fun j => ?_) hsa hsq
        have := abs_gk_le k (j + (n + 1))
        push_cast at this
        rw [show (j : ℝ) + (n + 1) = j + n + 1 by ring] at this
        exact this
    _ ≤ _ := tail_inv_sq n

/-- `C_k = ∑_{m ≤ n} g_k(m) + ∑_j g_k(j + n + 1)`. -/
theorem Ck_split (k n : ℕ) :
    Ck k = ∑ m ∈ Finset.Icc 1 n, gk k m + ∑' j, gk k (j + (n + 1)) := by
  unfold Ck
  rw [← (summable_gk k).sum_add_tsum_nat_add (n + 1)]
  congr 1
  rw [Finset.range_eq_Ico]
  have h : Finset.Ico 0 (n + 1) = insert 0 (Finset.Icc 1 n) := by
    ext m
    simp only [Finset.mem_Ico, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [h, Finset.sum_insert (by simp), gk_zero, zero_add]

/-! ## (3) The Euler product: `C_k·∏_{p ∣ k}(1 − p^{−2}) = 6/π²` -/

/-- `C₁ = ∑ μ(m)/m² = 1/ζ(2) = 6/π²` (Mathlib: `L(ζ, 2)·L(μ, 2) = 1`, `ζ(2) = π²/6`). -/
theorem Ck_one : Ck 1 = 6 / Real.pi ^ 2 := by
  have hL : LSeries (fun n => ((moebius n : ℤ) : ℂ)) 2 = ((Ck 1 : ℝ) : ℂ) := by
    unfold LSeries Ck
    rw [Complex.ofReal_tsum]
    congr 1
    funext n
    rw [LSeries.term_def]
    unfold gk
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [if_neg hn.ne', if_pos (Nat.coprime_one_right n)]
      push_cast
      rw [Complex.cpow_ofNat]
  have hz := LSeries_zeta_mul_Lseries_moebius (s := 2) (by norm_num)
  rw [LSeries_zeta_eq_riemannZeta (by norm_num), riemannZeta_two, hL] at hz
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h : ((Ck 1 : ℝ) : ℂ) = ((6 / Real.pi ^ 2 : ℝ) : ℂ) := by
    push_cast
    field_simp
    linear_combination 6 * hz
  exact_mod_cast h

/-- **Removing one prime**: `C_{kp}(1 − 1/p²) = C_k` for `p ∤ k`. -/
theorem Ck_prime (k p : ℕ) (hp : p.Prime) (hpk : ¬ p ∣ k) :
    Ck (k * p) * (1 - 1 / (p : ℝ) ^ 2) = Ck k := by
  have hpc : Nat.Coprime p k := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpk
  have hcp : ∀ m : ℕ, Nat.Coprime m p ↔ ¬ p ∣ m := fun m => by
    rw [Nat.coprime_comm]
    exact Nat.Prime.coprime_iff_not_dvd hp
  have hsplit : ∀ m, gk k m = gk (k * p) m + (if p ∣ m then gk k m else 0) := by
    intro m
    unfold gk
    by_cases hmk : Nat.Coprime m k
    · by_cases hpm : p ∣ m
      · rw [if_neg (fun h => ((hcp m).mp (Nat.coprime_mul_iff_right.mp h).2) hpm), if_pos hpm,
          zero_add]
      · rw [if_pos (Nat.coprime_mul_iff_right.mpr ⟨hmk, (hcp m).mpr hpm⟩), if_neg hpm,
          if_pos hmk, add_zero]
    · rw [if_neg hmk, if_neg (fun h => hmk (Nat.coprime_mul_iff_right.mp h).1)]
      split_ifs <;> simp
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hpj : ∀ j, gk k (p * j) = -(1 / (p : ℝ) ^ 2) * gk (k * p) j := by
    intro j
    unfold gk
    by_cases hjk : Nat.Coprime j k
    · have hc1 : Nat.Coprime (p * j) k := Nat.coprime_mul_iff_left.mpr ⟨hpc, hjk⟩
      rw [if_pos hc1]
      by_cases hdj : p ∣ j
      · have hns : ¬ Squarefree (p * j) := fun h =>
          (Nat.Prime.one_lt hp).ne' (Nat.isUnit_iff.mp (h p (mul_dvd_mul_left p hdj)))
        rw [moebius_eq_zero_of_not_squarefree hns,
          if_neg (fun h => ((hcp j).mp (Nat.coprime_mul_iff_right.mp h).2) hdj)]
        simp
      · have hpj' : Nat.Coprime p j := (Nat.Prime.coprime_iff_not_dvd hp).mpr hdj
        rw [if_pos (Nat.coprime_mul_iff_right.mpr ⟨hjk, (hcp j).mpr hdj⟩),
          isMultiplicative_moebius.map_mul_of_coprime hpj', moebius_apply_prime hp]
        push_cast
        rcases Nat.eq_zero_or_pos j with rfl | hj
        · simp
        · have hj0 : (j : ℝ) ≠ 0 := by exact_mod_cast hj.ne'
          field_simp
    · rw [if_neg (fun h => hjk (Nat.coprime_mul_iff_left.mp h).2),
        if_neg (fun h => hjk (Nat.coprime_mul_iff_right.mp h).1), mul_zero]
  have hs1 : Summable (gk (k * p)) := summable_gk _
  have hs2 : Summable (fun m => if p ∣ m then gk k m else 0) :=
    Summable.of_norm_bounded (summable_gk k).abs fun m => by
      rw [Real.norm_eq_abs]
      split_ifs
      · exact le_rfl
      · rw [abs_zero]
        exact abs_nonneg _
  have hmult : ∑' m, (if p ∣ m then gk k m else 0) = ∑' j, gk k (p * j) := by
    have hinj : Function.Injective (fun j : ℕ => p * j) := fun a b h =>
      Nat.eq_of_mul_eq_mul_left hp.pos h
    have hsupp : Function.support (fun m => if p ∣ m then gk k m else 0) ⊆
        Set.range (fun j : ℕ => p * j) := by
      intro m hm
      rw [Function.mem_support] at hm
      have hpm : p ∣ m := by
        by_contra h
        exact hm (if_neg h)
      obtain ⟨j, rfl⟩ := hpm
      exact ⟨j, rfl⟩
    rw [← hinj.tsum_eq hsupp]
    refine tsum_congr fun j => ?_
    simp only [dvd_mul_right, if_true]
  have hCk : Ck k = Ck (k * p) - 1 / (p : ℝ) ^ 2 * Ck (k * p) := by
    unfold Ck
    rw [tsum_congr hsplit, hs1.tsum_add hs2, hmult, tsum_congr hpj, tsum_mul_left]
    ring
  rw [hCk]
  ring

/-- **The Euler product over a set of primes**: `C_{∏S}·∏_{p ∈ S}(1 − 1/p²) = 6/π²`. -/
theorem Ck_prod (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    Ck (∏ p ∈ S, p) * ∏ p ∈ S, (1 - 1 / (p : ℝ) ^ 2) = 6 / Real.pi ^ 2 := by
  induction S using Finset.induction_on with
  | empty => simp [Ck_one]
  | insert p S hpS ih =>
    have hp : p.Prime := hS p (Finset.mem_insert_self p S)
    have ih' := ih fun q hq => hS q (Finset.mem_insert_of_mem hq)
    have hnd : ¬ p ∣ ∏ q ∈ S, q := by
      intro h
      obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finsetProd_iff hp.prime _).mp h
      have hqp : q.Prime := hS q (Finset.mem_insert_of_mem hq)
      have : p = q := (Nat.prime_dvd_prime_iff_eq hp hqp).mp hpq
      exact hpS (this ▸ hq)
    rw [Finset.prod_insert hpS, Finset.prod_insert hpS, mul_comm p, ← ih',
      ← Ck_prime _ p hp hnd]
    ring

open scoped ArithmeticFunction.zeta in
/-- **The density**: `(∑_{e ∣ k} μ(e)/e)·C_k = (6/π²)·k/σ(k)` for square-free `k`
(`∏(1 − 1/p)·∏(1 + p) = ∏p·∏(1 − 1/p²)`). -/
theorem main_const (k : ℕ) (hk : Squarefree k) :
    (∑ e ∈ k.divisors, ((moebius e : ℤ) : ℝ) / (e : ℝ)) * Ck k =
      6 / Real.pi ^ 2 * ((k : ℝ) / (sigma 1 k : ℝ)) := by
  set P := k.primeFactors with hPdef
  have hkP : ∏ p ∈ P, p = k := Nat.prod_primeFactors_of_squarefree hk
  have hE := Ck_prod P (fun p hp => Nat.prime_of_mem_primeFactors hp)
  rw [hkP] at hE
  have hν : ((ζ : ArithmeticFunction ℝ).pdiv ArithmeticFunction.id).IsMultiplicative :=
    isMultiplicative_zeta.natCast.pdiv isMultiplicative_id.natCast
  have hνv : ∀ n : ℕ, n ≠ 0 → ((ζ : ArithmeticFunction ℝ).pdiv ArithmeticFunction.id) n =
      1 / (n : ℝ) := by
    intro n hn
    simp [ArithmeticFunction.pdiv_apply, hn]
  have hA : ∑ e ∈ k.divisors, ((moebius e : ℤ) : ℝ) / (e : ℝ) =
      ∏ p ∈ P, (1 - 1 / (p : ℝ)) := by
    have h1 := IsMultiplicative.prodPrimeFactors_one_sub_of_squarefree _ hν hk
    calc ∑ e ∈ k.divisors, ((moebius e : ℤ) : ℝ) / (e : ℝ)
        = ∑ d ∈ k.divisors, (moebius : ArithmeticFunction ℝ) d *
            ((ζ : ArithmeticFunction ℝ).pdiv ArithmeticFunction.id) d := by
          refine Finset.sum_congr rfl fun d hd => ?_
          rw [intCoe_apply, hνv d (Nat.ne_of_gt (Nat.pos_of_mem_divisors hd))]
          ring
      _ = ∏ p ∈ k.primeFactors, (1 - ((ζ : ArithmeticFunction ℝ).pdiv
            ArithmeticFunction.id) p) := h1.symm
      _ = ∏ p ∈ P, (1 - 1 / (p : ℝ)) := by
          refine Finset.prod_congr rfl fun p hp => ?_
          rw [hνv p (Nat.prime_of_mem_primeFactors hp).ne_zero]
  have hC : (sigma 1 k : ℝ) = ∏ p ∈ P, (1 + (p : ℝ)) := by
    have h1 := isMultiplicative_id.prodPrimeFactors_one_add_of_squarefree hk
    rw [sigma_one_apply]
    have h2 : ∏ p ∈ P, (1 + (p : ℕ)) = ∑ d ∈ k.divisors, d := by
      rw [hPdef]
      simpa only [id_apply] using h1
    rw [← h2]
    push_cast
    rfl
  have hk' : (k : ℝ) = ∏ p ∈ P, (p : ℝ) := by
    rw [← hkP]
    push_cast
    rfl
  have hpt : (∏ p ∈ P, (1 - 1 / (p : ℝ))) * ∏ p ∈ P, (1 + (p : ℝ)) =
      (∏ p ∈ P, (p : ℝ)) * ∏ p ∈ P, (1 - 1 / (p : ℝ) ^ 2) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
    field_simp
    ring
  have hCpos : 0 < ∏ p ∈ P, (1 + (p : ℝ)) := Finset.prod_pos fun p _ => by positivity
  rw [hA, hC, hk', ← hE]
  field_simp
  linear_combination Ck k * hpt

/-! ## (4) The error of one divisor `e`, and `CountSq` -/

/-- `f(X) ≤ ⌊X⌋ + (X²/2)/(⌊X⌋ + 1/2) ≤ 1.5X`. -/
theorem f_bound (X : ℝ) (hX : 0 ≤ X) :
    (⌊X⌋₊ : ℝ) + X ^ 2 / 2 * (1 / ((⌊X⌋₊ : ℝ) + 1 / 2)) ≤ 1.5 * X := by
  set n := ⌊X⌋₊ with hn
  have h1 : (n : ℝ) ≤ X := Nat.floor_le hX
  have h2 : X < n + 1 := Nat.lt_floor_add_one X
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [mul_one_div, div_div]
  have hpos : 0 < 2 * ((n : ℝ) + 1 / 2) := by positivity
  have key : X ^ 2 ≤ (1.5 * X - n) * (2 * ((n : ℝ) + 1 / 2)) := by
    rcases Nat.eq_zero_or_pos n with h0 | hp
    · rw [h0] at h1 h2 ⊢
      push_cast at h1 h2 ⊢
      nlinarith
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hp
      nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2.le)]
  have : X ^ 2 / (2 * ((n : ℝ) + 1 / 2)) ≤ 1.5 * X - n := by
    rw [div_le_iff₀ hpos]
    exact key
  linarith

/-- `|(⌊b⌋/d − ⌊a⌋/d) − (b − a)/d| ≤ 1`. -/
theorem cnt_err (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (d : ℕ) (hd : 0 < d) :
    |(((⌊b⌋₊ / d - ⌊a⌋₊ / d : ℕ)) : ℝ) - (b - a) / d| ≤ 1 := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  rw [← Nat.floor_div_natCast b d, ← Nat.floor_div_natCast a d]
  have hle : ⌊a / d⌋₊ ≤ ⌊b / d⌋₊ := Nat.floor_le_floor (div_le_div_of_nonneg_right hab hd0.le)
  rw [Nat.cast_sub hle]
  have h1 := Nat.floor_le (div_nonneg (ha.trans hab) hd0.le : 0 ≤ b / d)
  have h2 := Nat.lt_floor_add_one (b / d)
  have h3 := Nat.floor_le (div_nonneg ha hd0.le : 0 ≤ a / d)
  have h4 := Nat.lt_floor_add_one (a / d)
  have e : (b - a) / d = b / d - a / d := sub_div b a d
  rw [e, abs_le]
  constructor <;> linarith

/-- **One divisor**: `|∑_{m ≤ ⌊b⌋, (m,k)=1} μ(m)·cnt(em²) − ((b − a)/e)·C_k| ≤ 1.5√(b/e)`. -/
theorem e_bound (k : ℕ) (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb2a : b ≤ 2 * a) (e : ℕ)
    (he : 0 < e) :
    |∑ m ∈ Finset.Icc 1 ⌊b⌋₊, (if Nat.Coprime m k then ((moebius m : ℤ) : ℝ) else 0) *
        (((⌊b⌋₊ / (e * m ^ 2) - ⌊a⌋₊ / (e * m ^ 2) : ℕ)) : ℝ) - (b - a) / e * Ck k| ≤
      1.5 * Real.sqrt (b / e) := by
  have he0 : (0 : ℝ) < e := by exact_mod_cast he
  have hb0 : 0 ≤ b := ha.trans hab
  set X := Real.sqrt (b / e) with hX
  have hX0 : 0 ≤ X := Real.sqrt_nonneg _
  have hX2 : X ^ 2 = b / e := Real.sq_sqrt (by positivity)
  set n := ⌊X⌋₊ with hn
  have hnX : (n : ℝ) ≤ X := Nat.floor_le hX0
  have hXn : X < n + 1 := Nat.lt_floor_add_one X
  have hnb : n ≤ ⌊b⌋₊ := by
    refine Nat.le_floor ?_
    have h1 : (n : ℝ) ^ 2 ≤ b / e := by rw [← hX2]; exact pow_le_pow_left₀ (Nat.cast_nonneg n) hnX 2
    have h2 : b / e ≤ b := div_le_self hb0 (by exact_mod_cast he)
    have h3 : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
      rcases Nat.eq_zero_or_pos n with h0 | hp
      · rw [h0]; simp
      · have : (1 : ℝ) ≤ n := by exact_mod_cast hp
        nlinarith
    linarith
  -- terms with m > n vanish
  have hzero : ∀ m ∈ Finset.Icc 1 ⌊b⌋₊, n < m →
      (((⌊b⌋₊ / (e * m ^ 2) - ⌊a⌋₊ / (e * m ^ 2) : ℕ)) : ℝ) = 0 := by
    intro m _ hm
    have hm1 : (n : ℝ) + 1 ≤ m := by exact_mod_cast hm
    have hXm : X < m := by linarith
    have hm2 : b < e * (m : ℝ) ^ 2 := by
      have : b / e < (m : ℝ) ^ 2 := by
        rw [← hX2]
        exact pow_lt_pow_left₀ hXm hX0 two_ne_zero
      rw [div_lt_iff₀ he0] at this
      linarith
    have hfb : ⌊b⌋₊ < e * m ^ 2 := by
      have : (⌊b⌋₊ : ℝ) < ((e * m ^ 2 : ℕ) : ℝ) := by
        push_cast
        exact lt_of_le_of_lt (Nat.floor_le hb0) hm2
      exact_mod_cast this
    have hfa : ⌊a⌋₊ ≤ ⌊b⌋₊ := Nat.floor_le_floor hab
    rw [Nat.div_eq_of_lt hfb, Nat.div_eq_of_lt (lt_of_le_of_lt hfa hfb)]
    simp
  have hsplit : Finset.Icc 1 ⌊b⌋₊ = Finset.Icc 1 n ∪ Finset.Ioc n ⌊b⌋₊ := by
    ext m
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
    omega
  have hdisj : Disjoint (Finset.Icc 1 n) (Finset.Ioc n ⌊b⌋₊) := by
    rw [Finset.disjoint_left]
    intro m h1 h2
    simp only [Finset.mem_Icc, Finset.mem_Ioc] at h1 h2
    omega
  rw [hsplit, Finset.sum_union hdisj]
  rw [Finset.sum_eq_zero (s := Finset.Ioc n ⌊b⌋₊) (fun m hm => by
    have hm' := Finset.mem_Ioc.mp hm
    rw [hzero m (Finset.mem_Icc.mpr ⟨by omega, hm'.2⟩) hm'.1, mul_zero]), add_zero]
  rw [Ck_split k n, mul_add, Finset.mul_sum, ← sub_sub, ← Finset.sum_sub_distrib]
  have hterm : ∀ m ∈ Finset.Icc 1 n,
      |(if Nat.Coprime m k then ((moebius m : ℤ) : ℝ) else 0) *
          (((⌊b⌋₊ / (e * m ^ 2) - ⌊a⌋₊ / (e * m ^ 2) : ℕ)) : ℝ) - (b - a) / e * gk k m| ≤ 1 := by
    intro m hm
    have hm1 : 0 < m := (Finset.mem_Icc.mp hm).1
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
    unfold gk
    by_cases hc : Nat.Coprime m k
    · rw [if_pos hc, if_pos hc]
      have hd : 0 < e * m ^ 2 := by positivity
      have hce := cnt_err a b ha hab (e * m ^ 2) hd
      have e1 : ((moebius m : ℤ) : ℝ) * (((⌊b⌋₊ / (e * m ^ 2) - ⌊a⌋₊ / (e * m ^ 2) : ℕ)) : ℝ) -
          (b - a) / e * (((moebius m : ℤ) : ℝ) / (m : ℝ) ^ 2) =
          ((moebius m : ℤ) : ℝ) * ((((⌊b⌋₊ / (e * m ^ 2) - ⌊a⌋₊ / (e * m ^ 2) : ℕ)) : ℝ) -
            (b - a) / ((e * m ^ 2 : ℕ) : ℝ)) := by
        push_cast
        field_simp
      rw [e1, abs_mul]
      have hmu : |((moebius m : ℤ) : ℝ)| ≤ 1 := by
        rw [← Int.cast_abs]
        exact_mod_cast abs_moebius_le_one
      calc |((moebius m : ℤ) : ℝ)| * |_| ≤ 1 * 1 :=
            mul_le_mul hmu hce (abs_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    · rw [if_neg hc, if_neg hc]
      simp
  have hsum1 : |∑ m ∈ Finset.Icc 1 n, ((if Nat.Coprime m k then ((moebius m : ℤ) : ℝ) else 0) *
      (((⌊b⌋₊ / (e * m ^ 2) - ⌊a⌋₊ / (e * m ^ 2) : ℕ)) : ℝ) - (b - a) / e * gk k m)| ≤ n := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum hterm).trans ?_
    simp
  have hba : 0 ≤ (b - a) / e := div_nonneg (by linarith) he0.le
  have hba2 : (b - a) / e ≤ X ^ 2 / 2 := by
    rw [hX2, div_le_iff₀ he0]
    field_simp
    linarith
  have htail := tail_gk k n
  have hsum2 : |(b - a) / e * ∑' j, gk k (j + (n + 1))| ≤ X ^ 2 / 2 * (1 / ((n : ℝ) + 1 / 2)) := by
    rw [abs_mul, abs_of_nonneg hba]
    exact mul_le_mul hba2 htail (abs_nonneg _) (by positivity)
  have hf := f_bound X hX0
  rw [← hn] at hf
  calc _ ≤ |∑ m ∈ Finset.Icc 1 n, ((if Nat.Coprime m k then ((moebius m : ℤ) : ℝ) else 0) *
          (((⌊b⌋₊ / (e * m ^ 2) - ⌊a⌋₊ / (e * m ^ 2) : ℕ)) : ℝ) - (b - a) / e * gk k m)| +
        |(b - a) / e * ∑' j, gk k (j + (n + 1))| := abs_sub _ _
    _ ≤ n + X ^ 2 / 2 * (1 / ((n : ℝ) + 1 / 2)) := add_le_add hsum1 hsum2
    _ ≤ 1.5 * X := hf

/-- **`M2B.CountSq`, PROVED**: Möbius inversion of `(l, k) = 1` and of square-freeness
(`nSq_expand`), the density `(∑_{e∣k} μ(e)/e)·C_k = (6/π²)k/σ(k)` (`main_const`, from Mathlib's
`ζ(2) = π²/6` and `L(ζ)·L(μ) = 1`), and per divisor `e` the error `≤ 1.5√(b/e)` (`e_bound`). -/
theorem countSq_holds : M2B.CountSq := by
  intro k hk a b ha hab hb2a
  have hk0 : k ≠ 0 := hk.ne_zero
  rw [nSq_expand k hk0 a b ha hab]
  have hmain : 6 / Real.pi ^ 2 * ((k : ℝ) / (sigma 1 k : ℝ)) * (b - a) =
      ∑ e ∈ k.divisors, ((moebius e : ℤ) : ℝ) * ((b - a) / e * Ck k) := by
    rw [← main_const k hk, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun e _ => ?_
    ring
  rw [hmain, ← Finset.sum_sub_distrib]
  have hfac : ∀ e ∈ k.divisors,
      (∑ m ∈ Finset.Icc 1 ⌊b⌋₊,
        (if Nat.Coprime m k then ((moebius e : ℤ) : ℝ) * ((moebius m : ℤ) : ℝ) else 0) *
          (((⌊b⌋₊ / (e * m ^ 2) - ⌊a⌋₊ / (e * m ^ 2) : ℕ)) : ℝ)) -
        ((moebius e : ℤ) : ℝ) * ((b - a) / e * Ck k) =
      ((moebius e : ℤ) : ℝ) * (∑ m ∈ Finset.Icc 1 ⌊b⌋₊,
        (if Nat.Coprime m k then ((moebius m : ℤ) : ℝ) else 0) *
          (((⌊b⌋₊ / (e * m ^ 2) - ⌊a⌋₊ / (e * m ^ 2) : ℕ)) : ℝ) - (b - a) / e * Ck k) := by
    intro e _
    rw [mul_sub, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    split_ifs <;> ring
  rw [Finset.sum_congr rfl hfac, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun e he => ?_)
  rw [abs_mul]
  have hmu : |((moebius e : ℤ) : ℝ)| ≤ 1 := by
    rw [← Int.cast_abs]
    exact_mod_cast abs_moebius_le_one
  have hE := e_bound k a b ha hab hb2a e (Nat.pos_of_mem_divisors he)
  calc |((moebius e : ℤ) : ℝ)| * |_| ≤ 1 * (1.5 * Real.sqrt (b / e)) :=
        mul_le_mul hmu hE (abs_nonneg _) zero_le_one
    _ = 1.5 * Real.sqrt (b / e) := one_mul _

/-- **`M2H.MonroFleming`, PROVED** (`M2B.monroFlem_of_monro2B` ∘ `M2B.monro2B_of_count`). -/
theorem monroFleming_holds : M2H.MonroFleming :=
  M2B.monroFlem_of_monro2B (M2B.monro2B_of_count countSq_holds)

end Principia.Common.TernaryGoldbach.M2Q
