/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Erdos1054.Spine
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.PSeries
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin

set_option autoImplicit false

/-!
# Erdős 1054 (EP1054.tex) — `lem:moment` (lines 562–638)

Proves `Spine.Link_Lem_Moment : Eq_Reflection → Lem_Moment`, i.e. for every `k ≥ 2` one constant
`C_k` satisfying `eq:Ck-growth`, `eq:moment` and `eq:large-count`.

**The constant.** The witness is `C_k = (k+2)^{2^{k+1}}`, not the paper's
`∏_{j=1}^{k+1} ζ(1+j/(k+1))^{\binom{k+1}{j}}` (`Statements.momentConst`): the lemma asserts only
the existence of a constant, and the paper's own proof of `eq:Ck-growth` bounds each of the
`2^{k+1} − 1` zeta factors by `1 + (k+1)/j ≤ k+2`, which is exactly what is used here, factor by
factor, on finite partial sums. `log C_k = 2^{k+1} log(k+2) ≤ 2^{k+1} log(2k+2)`.

**The proof** follows lines 584–637 for general `k`:

* `momentSum_eq` — expanding the `k`-th power: a sum over `(n, e, r₁, …, r_k) ∈ [1, ⌊Z⌋]^{k+2}`
  of `[e ∣ n, e > E] ∏ [e ≤ r_i, r_i ∣ n]/r_i` (`momJ`);
* `ydec` — the subset decomposition `y_S = ∏_p p^{#{t ≥ 1 : S_{p,t} = S}}` of lines 608–612 over
  all `S ⊆ {0,…,k}` (`y_∅ = 1`), with `x_i = ∏_{S ∋ i} y_S` (`ydec_prod_mem`),
  `∏ x_i = ∏_S y_S^{|S|}` (`prod_eq_prod_ydec_pow`), and `∏_S y_S ∣ n` for every common
  multiple `n` of the `x_i` (`prod_ydec_dvd`, the `lcm = ∏_S y_S` of line 614 in the only form
  used); `x ↦ y` is injective (`ydec_inj`);
* `sum_momJ_le` — counting common multiples (`#{n ≤ N : ∏ y_S ∣ n} ≤ N/∏ y_S`) and the pointwise
  weight bound `1/(r₁⋯r_k) ≤ E^{1-k} R^{-1/(k+1)}` (`pointwise_weight`, lines 598–607);
* `sum_momG_le` — the injection into `∏_S [1, N]` ("dropping the nesting restrictions", line 616)
  and `∑_{y ≤ N} y^{-1-|S|/(k+1)} ≤ 1 + (k+1)/|S| ≤ k + 2` (`partial_zeta_le`, from Mathlib's
  `ZetaAsymptotics.zeta_limit_aux1`);
* `largeCount_of_moment` — `eq:large-count` from `eq:reflection` and `eq:moment` for any `k`, `C_k`
  (lines 628–637: `N = n g_e(n)`, the pair `(n, e)` determines `N`, Markov).
-/

namespace Principia.Erdos1054.Proofs.Moment

open Finset

variable {m : ℕ}

/-- Level set `S_{p,t} = {i : t ≤ v_p(x_i)}`. -/
noncomputable def lev (x : Fin m → ℕ) (p t : ℕ) : Finset (Fin m) :=
  univ.filter (fun i => t ≤ (x i).factorization p)

/-- A uniform bound on the valuations of the entries. -/
def vB (x : Fin m → ℕ) : ℕ := ∑ i, x i

/-- `c_S(p) = #{t ∈ [1, vB] : S_{p,t} = S}`. -/
noncomputable def cS (x : Fin m → ℕ) (S : Finset (Fin m)) (p : ℕ) : ℕ :=
  ((Icc 1 (vB x)).filter (fun t => lev x p t = S)).card

/-- The primes dividing some entry. -/
def PS (x : Fin m → ℕ) : Finset ℕ := (∏ i, x i).primeFactors

/-- The subset decomposition `y_S = ∏_p p^{c_S(p)}` (and `y_∅ = 1`). -/
noncomputable def ydec (x : Fin m → ℕ) (S : Finset (Fin m)) : ℕ :=
  if S = ∅ then 1 else ∏ p ∈ PS x, p ^ cS x S p

lemma ydec_ne_zero (x : Fin m → ℕ) (S : Finset (Fin m)) : ydec x S ≠ 0 := by
  unfold ydec
  split_ifs with h
  · exact one_ne_zero
  · rw [Finset.prod_ne_zero_iff]
    intro p hp
    exact pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero

lemma ydec_factorization (x : Fin m → ℕ) (S : Finset (Fin m)) (q : ℕ) :
    (ydec x S).factorization q = if S = ∅ then 0 else if q ∈ PS x then cS x S q else 0 := by
  unfold ydec
  split_ifs with h hq
  · simp
  · rw [Nat.factorization_prod
      (fun p (hp : p ∈ PS x) => pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero),
      Finsupp.finsetSum_apply]
    rw [Finset.sum_eq_single q]
    · rw [(Nat.prime_of_mem_primeFactors hq).factorization_pow, Finsupp.single_eq_same]
    · intro p hp hpq
      rw [(Nat.prime_of_mem_primeFactors hp).factorization_pow, Finsupp.single_eq_of_ne' hpq]
    · intro h'
      exact absurd hq h'
  · rw [Nat.factorization_prod
      (fun p (hp : p ∈ PS x) => pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero),
      Finsupp.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro p hp
    rw [(Nat.prime_of_mem_primeFactors hp).factorization_pow, Finsupp.single_eq_of_ne']
    rintro rfl
    exact hq hp

lemma factorization_eq_zero_of_notMem_PS (x : Fin m → ℕ) (hx : ∀ i, x i ≠ 0) {q : ℕ}
    (hq : q ∉ PS x) (i : Fin m) : (x i).factorization q = 0 := by
  by_contra h
  apply hq
  have hmem : q ∈ (x i).primeFactors := by
    rw [← Nat.support_factorization]
    exact Finsupp.mem_support_iff.mpr h
  exact Nat.primeFactors_mono (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))
    (Finset.prod_ne_zero_iff.mpr (fun j _ => hx j)) hmem

lemma factorization_le_vB (x : Fin m → ℕ) (hx : ∀ i, x i ≠ 0) (q : ℕ) (i : Fin m) :
    (x i).factorization q ≤ vB x :=
  (Nat.factorization_lt q (hx i)).le.trans
    (Finset.single_le_sum (fun j _ => Nat.zero_le (x j)) (Finset.mem_univ i))

lemma sum_cS (x : Fin m → ℕ) (T : Finset (Finset (Fin m))) (q : ℕ) :
    ∑ S ∈ T, cS x S q = ((Icc 1 (vB x)).filter (fun t => lev x q t ∈ T)).card := by
  unfold cS
  exact Finset.sum_card_fiberwise_eq_card_filter _ _ _

/-- Each entry is the product of the `y_S` over the sets `S` containing its index. -/
lemma ydec_prod_mem (x : Fin m → ℕ) (hx : ∀ i, x i ≠ 0) (i : Fin m) :
    x i = ∏ S ∈ univ.filter (fun S : Finset (Fin m) => i ∈ S), ydec x S := by
  apply Nat.eq_of_factorization_eq (hx i)
    (Finset.prod_ne_zero_iff.mpr (fun S _ => ydec_ne_zero x S))
  intro q
  rw [Nat.factorization_prod (fun S _ => ydec_ne_zero x S), Finsupp.finsetSum_apply]
  have hS : ∀ S ∈ univ.filter (fun S : Finset (Fin m) => i ∈ S),
      (ydec x S).factorization q = if q ∈ PS x then cS x S q else 0 := by
    intro S hS
    rw [ydec_factorization, if_neg]
    rintro rfl
    simp at hS
  rw [Finset.sum_congr rfl hS]
  by_cases hq : q ∈ PS x
  · simp only [if_pos hq]
    rw [sum_cS]
    have hB := factorization_le_vB x hx q i
    have hset : ((Icc 1 (vB x)).filter
        (fun t => lev x q t ∈ univ.filter (fun S : Finset (Fin m) => i ∈ S)))
        = Icc 1 ((x i).factorization q) := by
      ext t
      simp only [mem_filter, mem_Icc, mem_univ, true_and, lev]
      constructor
      · rintro ⟨⟨h1, _⟩, h2⟩
        exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨h1, h2.trans hB⟩, h2⟩
    rw [hset, Nat.card_Icc]
    omega
  · simp only [if_neg hq, Finset.sum_const_zero]
    exact factorization_eq_zero_of_notMem_PS x hx hq i

/-- The product of all `y_S` divides every common multiple of the entries. -/
lemma prod_ydec_dvd (x : Fin m → ℕ) (hx : ∀ i, x i ≠ 0) {n : ℕ} (hn : n ≠ 0)
    (hdvd : ∀ i, x i ∣ n) : (∏ S, ydec x S) ∣ n := by
  have hY : (∏ S, ydec x S) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun S _ => ydec_ne_zero x S)
  rw [← Nat.factorization_le_iff_dvd hY hn, Finsupp.le_def]
  intro q
  rw [Nat.factorization_prod (fun S _ => ydec_ne_zero x S), Finsupp.finsetSum_apply,
    Finset.sum_congr rfl (fun S _ => ydec_factorization x S q)]
  by_cases hq : q ∈ PS x
  · simp only [if_pos hq]
    rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, sum_cS]
    calc _ ≤ (Icc 1 (n.factorization q)).card := by
          apply Finset.card_le_card
          intro t ht
          simp only [mem_filter, mem_Icc, mem_univ, true_and] at ht ⊢
          obtain ⟨⟨h1, _⟩, hne⟩ := ht
          obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr hne
          simp only [lev, mem_filter, mem_univ, true_and] at hj
          exact ⟨h1, hj.trans (Finsupp.le_def.mp
            ((Nat.factorization_le_iff_dvd (hx j) hn).mpr (hdvd j)) q)⟩
      _ = n.factorization q := by rw [Nat.card_Icc]; omega
  · simp only [if_neg hq, ite_self, Finset.sum_const_zero]
    exact Nat.zero_le _

/-- `∏ x_i = ∏_S y_S^{|S|}`. -/
lemma prod_eq_prod_ydec_pow (x : Fin m → ℕ) (hx : ∀ i, x i ≠ 0) :
    ∏ i, x i = ∏ S, ydec x S ^ S.card := by
  calc ∏ i, x i = ∏ i, ∏ S ∈ univ.filter (fun S : Finset (Fin m) => i ∈ S), ydec x S :=
        Finset.prod_congr rfl (fun i _ => ydec_prod_mem x hx i)
    _ = ∏ S, ∏ i ∈ S, ydec x S := by
        apply Finset.prod_comm'
        intro i S
        simp
    _ = ∏ S, ydec x S ^ S.card := Finset.prod_congr rfl (fun S _ => Finset.prod_const _)

lemma ydec_dvd (x : Fin m → ℕ) (hx : ∀ i, x i ≠ 0) {S : Finset (Fin m)} {i : Fin m}
    (hi : i ∈ S) : ydec x S ∣ x i := by
  rw [ydec_prod_mem x hx i]
  exact Finset.dvd_prod_of_mem _ (by simp [hi])

lemma ydec_inj {x x' : Fin m → ℕ} (hx : ∀ i, x i ≠ 0) (hx' : ∀ i, x' i ≠ 0)
    (h : ydec x = ydec x') : x = x' := by
  funext i
  rw [ydec_prod_mem x hx i, ydec_prod_mem x' hx' i, h]


/-! ## Analytic inputs -/

/-- Partial sums of `ζ(1+θ)`: `∑_{n ≤ N} n^{-(1+θ)} ≤ 1 + 1/θ` (from Mathlib's
`ZetaAsymptotics.zeta_limit_aux1`, i.e. `ζ(s) ≤ 1 + 1/(s-1)` for `s > 1`). -/
lemma partial_zeta_le (θ : ℝ) (hθ : 0 < θ) (N : ℕ) :
    ∑ n ∈ Icc 1 N, (n : ℝ) ^ (-(1 + θ)) ≤ 1 + 1 / θ := by
  have hs : 1 < 1 + θ := by linarith
  have hsum : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ (1 + θ)) := by
    have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_rpow.mpr hs)
    exact_mod_cast this
  have hre : ∀ M : ℕ, ∑ n ∈ Icc 1 M, (n : ℝ) ^ (-(1 + θ))
      = ∑ i ∈ range M, 1 / ((i : ℝ) + 1) ^ (1 + θ) := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ, Nat.cast_succ,
        Real.rpow_neg (by positivity), one_div]
  rw [hre N]
  have h1 : ∑ i ∈ range N, 1 / ((i : ℝ) + 1) ^ (1 + θ)
      ≤ ∑' i : ℕ, 1 / ((i : ℝ) + 1) ^ (1 + θ) :=
    hsum.sum_le_tsum (range N) (fun i _ => by positivity)
  have h2 := ZetaAsymptotics.zeta_limit_aux1 hs
  rw [show 1 + θ - 1 = θ by ring] at h2
  have hT : 0 ≤ ZetaAsymptotics.termTSum (1 + θ) :=
    tsum_nonneg (fun n => ZetaAsymptotics.term_nonneg (n + 1) (1 + θ))
  have h3 : 0 ≤ (1 + θ) * ZetaAsymptotics.termTSum (1 + θ) := mul_nonneg (by linarith) hT
  linarith

/-- The pointwise weight bound of lines 598–607: for `r₁ ⋯ r_k = P ≥ e^k` and `e ≥ E > 0`,
`1/P ≤ E^{1-k} (eP)^{-1/(k+1)}`. -/
lemma pointwise_weight (k : ℕ) (hk : 1 ≤ k) (E e P : ℝ) (hE : 0 < E) (hEe : E ≤ e)
    (hP : e ^ k ≤ P) :
    1 / P ≤ E ^ (1 - (k : ℝ)) * (e * P) ^ (-((k : ℝ) + 1)⁻¹) := by
  have he : 0 < e := hE.trans_le hEe
  have hP0 : 0 < P := lt_of_lt_of_le (pow_pos he k) hP
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have h1 : e ^ (1 - (k : ℝ)) ≤ E ^ (1 - (k : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hE hEe (by linarith)
  have h2 : e ^ (1 - (k : ℝ)) = e / e ^ k := by
    rw [Real.rpow_sub he, Real.rpow_one, Real.rpow_natCast]
  have ha0 : 0 < (e * P) ^ (((k : ℝ) + 1)⁻¹) := Real.rpow_pos_of_pos (by positivity) _
  have ham : ((e * P) ^ (((k : ℝ) + 1)⁻¹)) ^ (k + 1) = e * P := by
    rw [show ((k : ℝ) + 1) = ((k + 1 : ℕ) : ℝ) by push_cast; ring]
    exact Real.rpow_inv_natCast_pow (by positivity) (by omega)
  have h3 : (e * P) ^ (-((k : ℝ) + 1)⁻¹) = ((e * P) ^ (((k : ℝ) + 1)⁻¹))⁻¹ := by
    rw [Real.rpow_neg (by positivity)]
  set a := (e * P) ^ (((k : ℝ) + 1)⁻¹) with ha
  have hkey : e ^ k * a ≤ e * P := by
    have hPk : (e ^ k) ^ k ≤ P ^ k := pow_le_pow_left₀ (by positivity) hP k
    have hpow : (e ^ k * a) ^ (k + 1) ≤ (e * P) ^ (k + 1) := by
      calc (e ^ k * a) ^ (k + 1) = (e ^ k) ^ k * (e ^ k * e * P) := by
            rw [mul_pow, ham]; ring
        _ ≤ P ^ k * (e ^ k * e * P) := mul_le_mul_of_nonneg_right hPk (by positivity)
        _ = (e * P) ^ (k + 1) := by ring
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by omega)).mp hpow
  have hstep : 1 / P ≤ e ^ (1 - (k : ℝ)) * a⁻¹ := by
    rw [h2, show e / e ^ k * a⁻¹ = e / (e ^ k * a) by
      rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv, mul_assoc]]
    rw [div_le_div_iff₀ hP0 (by positivity)]
    linarith
  rw [h3]
  exact hstep.trans (mul_le_mul_of_nonneg_right h1 (inv_nonneg.mpr ha0.le))

/-- The weight `n^{-1} (n^c)^{-θ} = n^{-1 - cθ}` attached to a set of size `c`. -/
noncomputable def momWt (θ : ℝ) (c n : ℕ) : ℝ := (n : ℝ)⁻¹ * ((n : ℝ) ^ c) ^ (-θ)

lemma momWt_nonneg (θ : ℝ) (c n : ℕ) : 0 ≤ momWt θ c n := by
  unfold momWt
  exact mul_nonneg (by positivity) (Real.rpow_nonneg (by positivity) _)

/-- `G(y) = ∏_S y_S^{-1-|S|θ}`. -/
noncomputable def momG (θ : ℝ) (y : Finset (Fin m) → ℕ) : ℝ :=
  ∏ S, momWt θ S.card (y S)

lemma momG_nonneg (θ : ℝ) (y : Finset (Fin m) → ℕ) : 0 ≤ momG θ y :=
  Finset.prod_nonneg (fun _ _ => momWt_nonneg θ _ _)

lemma momG_eq (θ : ℝ) (y : Finset (Fin m) → ℕ) :
    momG θ y = (∏ S, (y S : ℝ))⁻¹ * (∏ S, ((y S : ℝ)) ^ S.card) ^ (-θ) := by
  unfold momG momWt
  rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib,
    Real.finsetProd_rpow _ _ (fun S _ => by positivity)]

/-- A factor of the Euler-type product: `∑_{n ≤ N} n^{-1-cθ} ≤ 1 + 1/θ` when `c ≥ 1`. -/
lemma sum_momWt_le (θ : ℝ) (hθ : 0 < θ) (c N : ℕ) (hc : 1 ≤ c) :
    ∑ n ∈ Icc 1 N, momWt θ c n ≤ 1 + 1 / θ := by
  refine le_trans (Finset.sum_le_sum (fun n hn => ?_)) (partial_zeta_le θ hθ N)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
  have hn0 : (0 : ℝ) < n := by linarith
  unfold momWt
  have hle : ((n : ℝ) ^ c) ^ (-θ) ≤ (n : ℝ) ^ (-θ) :=
    Real.rpow_le_rpow_of_nonpos hn0 (le_self_pow₀ hn1 (by omega)) (by linarith)
  calc (n : ℝ)⁻¹ * ((n : ℝ) ^ c) ^ (-θ) ≤ (n : ℝ)⁻¹ * (n : ℝ) ^ (-θ) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
    _ = (n : ℝ) ^ (-(1 + θ)) := by
        rw [← Real.rpow_neg_one, ← Real.rpow_add hn0]
        ring_nf

/-! ## The moment expansion -/

/-- `[e ≤ r, r ∣ n] / r`. -/
noncomputable def momInd (e r n : ℕ) : ℝ := if e ≤ r ∧ r ∣ n then (1 : ℝ) / r else 0

lemma momInd_nonneg (e r n : ℕ) : 0 ≤ momInd e r n := by
  unfold momInd
  split_ifs <;> positivity

lemma momInd_le (e r n : ℕ) : momInd e r n ≤ (1 : ℝ) / r := by
  unfold momInd
  split_ifs <;> [exact le_rfl; positivity]

/-- The summand `[e ∣ n, e > E] ∏_i [e ≤ r_i, r_i ∣ n]/r_i`. -/
noncomputable def momJ (E : ℝ) {k : ℕ} (n e : ℕ) (ρ : Fin k → ℕ) : ℝ :=
  (if e ∣ n ∧ E < (e : ℝ) then (1 : ℝ) else 0) * ∏ i, momInd e (ρ i) n

lemma g_eq_sum_momInd (N n e : ℕ) (hn : n ∈ Icc 1 N) :
    g e n = ∑ r ∈ Icc 1 N, momInd e r n := by
  rw [Finset.mem_Icc] at hn
  simp only [g, momInd]
  rw [← Finset.sum_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext r
  simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hrn, _⟩, her⟩
    exact ⟨⟨Nat.pos_of_dvd_of_pos hrn (by omega), (Nat.le_of_dvd (by omega) hrn).trans hn.2⟩,
      her, hrn⟩
  · rintro ⟨_, her, hrn⟩
    exact ⟨⟨hrn, by omega⟩, her⟩

lemma sum_divisors_filter_eq (E : ℝ) (N n : ℕ) (hn : n ∈ Icc 1 N) (f : ℕ → ℝ) :
    ∑ e ∈ n.divisors.filter (fun e : ℕ => E < (e : ℝ)), f e
      = ∑ e ∈ Icc 1 N, if e ∣ n ∧ E < (e : ℝ) then f e else 0 := by
  rw [Finset.mem_Icc] at hn
  rw [← Finset.sum_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext e
  simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hen, _⟩, hE'⟩
    exact ⟨⟨Nat.pos_of_dvd_of_pos hen (by omega), (Nat.le_of_dvd (by omega) hen).trans hn.2⟩,
      hen, hE'⟩
  · rintro ⟨_, hen, hE'⟩
    exact ⟨⟨hen, by omega⟩, hE'⟩

/-- Expanding the `k`-th power (line 587): the moment sum as a sum over `(n, e, r₁,…,r_k)`. -/
lemma momentSum_eq (k : ℕ) (E Z : ℝ) :
    momentSum k E Z = ∑ n ∈ Icc 1 ⌊Z⌋₊, ∑ e ∈ Icc 1 ⌊Z⌋₊,
      ∑ ρ ∈ Fintype.piFinset (fun _ : Fin k => Icc 1 ⌊Z⌋₊), momJ E n e ρ := by
  unfold momentSum
  refine Finset.sum_congr rfl (fun n hn => ?_)
  rw [sum_divisors_filter_eq E ⌊Z⌋₊ n hn]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  rw [g_eq_sum_momInd ⌊Z⌋₊ n e hn, Finset.sum_pow']
  unfold momJ
  rw [← Finset.mul_sum]
  split_ifs <;> simp

lemma cons_mem_Icc {k N e : ℕ} {ρ : Fin k → ℕ} (he : e ∈ Icc 1 N) (hρ : ∀ i, ρ i ∈ Icc 1 N)
    (j : Fin (k + 1)) : (Fin.cons e ρ : Fin (k + 1) → ℕ) j ∈ Icc 1 N := by
  refine Fin.cases ?_ (fun i => ?_) j
  · simpa using he
  · simpa using hρ i

lemma cons_ne_zero {k N e : ℕ} {ρ : Fin k → ℕ} (he : e ∈ Icc 1 N) (hρ : ∀ i, ρ i ∈ Icc 1 N)
    (j : Fin (k + 1)) : (Fin.cons e ρ : Fin (k + 1) → ℕ) j ≠ 0 := by
  have := (Finset.mem_Icc.mp (cons_mem_Icc he hρ j)).1
  omega

/-- One `(e, r₁, …, r_k)`-term (lines 588–607): counting common multiples, `⌊Z/lcm⌋ ≤ Z/lcm`,
the subset decomposition, and the pointwise weight bound. -/
lemma sum_momJ_le (k : ℕ) (hk : 1 ≤ k) (E : ℝ) (hE : 0 < E) (N e : ℕ) (ρ : Fin k → ℕ)
    (he : e ∈ Icc 1 N) (hρ : ∀ i, ρ i ∈ Icc 1 N) :
    ∑ n ∈ Icc 1 N, momJ E n e ρ
      ≤ (N : ℝ) * E ^ (1 - (k : ℝ))
        * momG ((k : ℝ) + 1)⁻¹ (ydec (Fin.cons e ρ : Fin (k + 1) → ℕ)) := by
  classical
  set x : Fin (k + 1) → ℕ := Fin.cons e ρ with hx_def
  have hx : ∀ j, x j ≠ 0 := cons_ne_zero he hρ
  have hGnn := momG_nonneg ((k : ℝ) + 1)⁻¹ (ydec x)
  have hRHS : 0 ≤ (N : ℝ) * E ^ (1 - (k : ℝ)) :=
    mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hE.le _)
  have hPi : 0 ≤ ∏ i, (1 : ℝ) / ρ i := Finset.prod_nonneg (fun i _ => by positivity)
  by_cases hc : E < (e : ℝ) ∧ ∀ i, e ≤ ρ i
  · set Y : ℕ := ∏ S, ydec x S with hY_def
    have hJle : ∀ n ∈ Icc 1 N, momJ E n e ρ ≤ (if Y ∣ n then (1 : ℝ) else 0) * ∏ i, (1 : ℝ) / ρ i := by
      intro n hn
      have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.mp hn).1; omega
      unfold momJ
      by_cases h1 : e ∣ n ∧ E < (e : ℝ)
      · by_cases h2 : ∀ i, ρ i ∣ n
        · have hYn : Y ∣ n := by
            refine prod_ydec_dvd x hx hn0 (fun j => ?_)
            refine Fin.cases ?_ (fun i => ?_) j
            · simpa [hx_def] using h1.1
            · simpa [hx_def] using h2 i
          rw [if_pos h1, if_pos hYn, one_mul, one_mul]
          apply le_of_eq
          refine Finset.prod_congr rfl (fun i _ => ?_)
          unfold momInd
          rw [if_pos ⟨hc.2 i, h2 i⟩]
        · push Not at h2
          obtain ⟨i, hi⟩ := h2
          rw [Finset.prod_eq_zero (Finset.mem_univ i)
            (by unfold momInd; rw [if_neg (fun h => hi h.2)]), mul_zero]
          exact mul_nonneg (by split_ifs <;> norm_num) hPi
      · rw [if_neg h1, zero_mul]
        exact mul_nonneg (by split_ifs <;> norm_num) hPi
    have hYpos : 0 < Y := Nat.pos_of_ne_zero
      (Finset.prod_ne_zero_iff.mpr (fun S _ => ydec_ne_zero x S))
    have hcard : ((((Icc 1 N).filter (fun n => Y ∣ n)).card : ℕ) : ℝ) ≤ (N : ℝ) / (Y : ℝ) := by
      have hc1 : ((Icc 1 N).filter (fun n => Y ∣ n)).card ≤ N / Y := by
        rw [← Nat.card_multiples' N Y]
        apply Finset.card_le_card
        intro n hn
        simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range] at hn ⊢
        exact ⟨by omega, by omega, hn.2⟩
      exact (Nat.cast_le.mpr hc1).trans Nat.cast_div_le
    -- the weight identity
    have hprodR : ∏ S, ((ydec x S : ℝ)) ^ S.card = (e : ℝ) * ∏ i, (ρ i : ℝ) := by
      have h := prod_eq_prod_ydec_pow x hx
      rw [hx_def, Fin.prod_cons] at h
      have h' : ((e * ∏ i, ρ i : ℕ) : ℝ) = ((∏ S, ydec (Fin.cons e ρ : Fin (k + 1) → ℕ) S ^ S.card : ℕ) : ℝ) := by
        rw [h]
      push_cast at h'
      rw [hx_def, ← h']
    have hG : momG ((k : ℝ) + 1)⁻¹ (ydec x)
        = (Y : ℝ)⁻¹ * ((e : ℝ) * ∏ i, (ρ i : ℝ)) ^ (-((k : ℝ) + 1)⁻¹) := by
      rw [momG_eq, hprodR, hY_def]
      push_cast
      ring
    have hPk : (e : ℝ) ^ k ≤ ∏ i, (ρ i : ℝ) := by
      calc (e : ℝ) ^ k = ∏ _i : Fin k, (e : ℝ) := by rw [Finset.prod_const, Finset.card_univ,
            Fintype.card_fin]
        _ ≤ ∏ i, (ρ i : ℝ) := Finset.prod_le_prod (fun _ _ => by positivity)
            (fun i _ => by exact_mod_cast hc.2 i)
    have hpw := pointwise_weight k hk E e (∏ i, (ρ i : ℝ)) hE hc.1.le hPk
    have hPi_eq : ∏ i, (1 : ℝ) / ρ i = 1 / ∏ i, (ρ i : ℝ) := by
      rw [Finset.prod_div_distrib, Finset.prod_const_one]
    calc ∑ n ∈ Icc 1 N, momJ E n e ρ
        ≤ ∑ n ∈ Icc 1 N, (if Y ∣ n then (1 : ℝ) else 0) * ∏ i, (1 : ℝ) / ρ i :=
          Finset.sum_le_sum hJle
      _ = ((((Icc 1 N).filter (fun n => Y ∣ n)).card : ℕ) : ℝ) * ∏ i, (1 : ℝ) / ρ i := by
          rw [← Finset.sum_mul, Finset.sum_boole]
      _ ≤ ((N : ℝ) / (Y : ℝ)) * ∏ i, (1 : ℝ) / ρ i := mul_le_mul_of_nonneg_right hcard hPi
      _ ≤ ((N : ℝ) / (Y : ℝ)) * (E ^ (1 - (k : ℝ))
            * ((e : ℝ) * ∏ i, (ρ i : ℝ)) ^ (-((k : ℝ) + 1)⁻¹)) := by
          rw [hPi_eq]
          exact mul_le_mul_of_nonneg_left hpw (by positivity)
      _ = (N : ℝ) * E ^ (1 - (k : ℝ)) * momG ((k : ℝ) + 1)⁻¹ (ydec x) := by
          rw [hG]
          ring
  · have hzero : ∀ n ∈ Icc 1 N, momJ E n e ρ = 0 := by
      intro n _
      unfold momJ
      by_cases h1 : e ∣ n ∧ E < (e : ℝ)
      · have : ∃ i, ρ i < e := by
          by_contra hne
          push Not at hne
          exact hc ⟨h1.2, hne⟩
        obtain ⟨i, hi⟩ := this
        rw [Finset.prod_eq_zero (Finset.mem_univ i)
          (by unfold momInd; rw [if_neg (fun h => by omega)]), mul_zero]
      · rw [if_neg h1, zero_mul]
    rw [Finset.sum_eq_zero hzero]
    exact mul_nonneg hRHS hGnn

/-- The subset-decomposition injection (lines 608–625): summing `G(y(e, r))` over all
`(e, r) ∈ [1,N]^{k+1}` is at most `∏_S ∑_y y^{-1-|S|/(k+1)} ≤ (k+2)^{2^{k+1}}`. -/
lemma sum_momG_le (k N : ℕ) :
    ∑ e ∈ Icc 1 N, ∑ ρ ∈ Fintype.piFinset (fun _ : Fin k => Icc 1 N),
      momG ((k : ℝ) + 1)⁻¹ (ydec (Fin.cons e ρ : Fin (k + 1) → ℕ))
      ≤ ((k : ℝ) + 2) ^ (2 ^ (k + 1)) := by
  classical
  set θ : ℝ := ((k : ℝ) + 1)⁻¹ with hθ
  have hθ0 : 0 < θ := by positivity
  set tS : Finset (Fin (k + 1)) → Finset ℕ := fun S => if S = ∅ then {1} else Icc 1 N with htS
  set φ : ℕ × (Fin k → ℕ) → Finset (Fin (k + 1)) → ℕ :=
    fun p => ydec (Fin.cons p.1 p.2 : Fin (k + 1) → ℕ) with hφ
  set D := Icc 1 N ×ˢ Fintype.piFinset (fun _ : Fin k => Icc 1 N) with hD
  have hmemD : ∀ p ∈ D, p.1 ∈ Icc 1 N ∧ ∀ i, p.2 i ∈ Icc 1 N := by
    intro p hp
    rw [hD, Finset.mem_product, Fintype.mem_piFinset] at hp
    exact hp
  have hinj : Set.InjOn φ ↑D := by
    intro p hp q hq hpq
    obtain ⟨hp1, hp2⟩ := hmemD p hp
    obtain ⟨hq1, hq2⟩ := hmemD q hq
    have := ydec_inj (cons_ne_zero hp1 hp2) (cons_ne_zero hq1 hq2) hpq
    rw [Fin.cons_inj] at this
    exact Prod.ext this.1 this.2
  have hsub : D.image φ ⊆ Fintype.piFinset tS := by
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨p, hp, rfl⟩ := hy
    obtain ⟨hp1, hp2⟩ := hmemD p hp
    rw [Fintype.mem_piFinset]
    intro S
    by_cases hS : S = ∅
    · simp only [htS, hφ, if_pos hS]
      unfold ydec
      rw [if_pos hS]
      exact Finset.mem_singleton_self 1
    · simp only [htS, hφ, if_neg hS]
      obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr hS
      have hdvd := ydec_dvd _ (cons_ne_zero hp1 hp2) hj
      have hxj := Finset.mem_Icc.mp (cons_mem_Icc hp1 hp2 j)
      have hpos := Nat.pos_of_ne_zero (ydec_ne_zero (Fin.cons p.1 p.2 : Fin (k + 1) → ℕ) S)
      rw [Finset.mem_Icc]
      exact ⟨hpos, (Nat.le_of_dvd (by omega) hdvd).trans hxj.2⟩
  have hfactor : ∀ S : Finset (Fin (k + 1)), ∑ n ∈ tS S, momWt θ S.card n ≤ (k : ℝ) + 2 := by
    intro S
    by_cases hS : S = ∅
    · simp only [htS, if_pos hS, Finset.sum_singleton]
      subst hS
      unfold momWt
      simp only [Finset.card_empty, pow_zero, Nat.cast_one, inv_one, Real.one_rpow, one_mul]
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith
    · simp only [htS, if_neg hS]
      have hc : 1 ≤ S.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hS)
      calc ∑ n ∈ Icc 1 N, momWt θ S.card n ≤ 1 + 1 / θ := sum_momWt_le θ hθ0 S.card N hc
        _ = (k : ℝ) + 2 := by rw [hθ, one_div, inv_inv]; ring
  rw [← Finset.sum_product' (s := Icc 1 N) (t := Fintype.piFinset (fun _ : Fin k => Icc 1 N))
    (f := fun e ρ => momG θ (ydec (Fin.cons e ρ : Fin (k + 1) → ℕ)))]
  change ∑ p ∈ D, momG θ (φ p) ≤ _
  rw [← Finset.sum_image hinj]
  calc ∑ y ∈ D.image φ, momG θ y ≤ ∑ y ∈ Fintype.piFinset tS, momG θ y :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun y _ _ => momG_nonneg θ y)
    _ = ∏ S, ∑ n ∈ tS S, momWt θ S.card n := by
        unfold momG
        rw [Finset.prod_univ_sum]
    _ ≤ ∏ _S : Finset (Fin (k + 1)), ((k : ℝ) + 2) :=
        Finset.prod_le_prod (fun S _ => Finset.sum_nonneg (fun n _ => momWt_nonneg θ _ _))
          (fun S _ => hfactor S)
    _ = ((k : ℝ) + 2) ^ (2 ^ (k + 1)) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_finset, Fintype.card_fin]

/-- **`eq:moment`** with the explicit constant `(k+2)^{2^{k+1}}`. -/
theorem moment_bound (k : ℕ) (hk : 2 ≤ k) (E Z : ℝ) (hE : 1 ≤ E) (hZ : 0 ≤ Z) :
    momentSum k E Z ≤ ((k : ℝ) + 2) ^ (2 ^ (k + 1)) * Z * E ^ (1 - (k : ℝ)) := by
  have hE0 : 0 < E := by linarith
  have hRHS : 0 ≤ (⌊Z⌋₊ : ℝ) * E ^ (1 - (k : ℝ)) :=
    mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hE0.le _)
  rw [momentSum_eq, Finset.sum_comm]
  calc ∑ e ∈ Icc 1 ⌊Z⌋₊, ∑ n ∈ Icc 1 ⌊Z⌋₊,
        ∑ ρ ∈ Fintype.piFinset (fun _ : Fin k => Icc 1 ⌊Z⌋₊), momJ E n e ρ
      = ∑ e ∈ Icc 1 ⌊Z⌋₊, ∑ ρ ∈ Fintype.piFinset (fun _ : Fin k => Icc 1 ⌊Z⌋₊),
        ∑ n ∈ Icc 1 ⌊Z⌋₊, momJ E n e ρ :=
        Finset.sum_congr rfl (fun e _ => Finset.sum_comm)
    _ ≤ ∑ e ∈ Icc 1 ⌊Z⌋₊, ∑ ρ ∈ Fintype.piFinset (fun _ : Fin k => Icc 1 ⌊Z⌋₊),
        (⌊Z⌋₊ : ℝ) * E ^ (1 - (k : ℝ))
          * momG ((k : ℝ) + 1)⁻¹ (ydec (Fin.cons e ρ : Fin (k + 1) → ℕ)) := by
        refine Finset.sum_le_sum (fun e he => Finset.sum_le_sum (fun ρ hρ => ?_))
        exact sum_momJ_le k (by omega) E hE0 ⌊Z⌋₊ e ρ he (Fintype.mem_piFinset.mp hρ)
    _ = (⌊Z⌋₊ : ℝ) * E ^ (1 - (k : ℝ)) * ∑ e ∈ Icc 1 ⌊Z⌋₊,
        ∑ ρ ∈ Fintype.piFinset (fun _ : Fin k => Icc 1 ⌊Z⌋₊),
          momG ((k : ℝ) + 1)⁻¹ (ydec (Fin.cons e ρ : Fin (k + 1) → ℕ)) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun e _ => by rw [Finset.mul_sum])
    _ ≤ (⌊Z⌋₊ : ℝ) * E ^ (1 - (k : ℝ)) * ((k : ℝ) + 2) ^ (2 ^ (k + 1)) :=
        mul_le_mul_of_nonneg_left (sum_momG_le k ⌊Z⌋₊) hRHS
    _ ≤ Z * E ^ (1 - (k : ℝ)) * ((k : ℝ) + 2) ^ (2 ^ (k + 1)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (Nat.floor_le hZ) (Real.rpow_nonneg hE0.le _))
          (by positivity)
    _ = ((k : ℝ) + 2) ^ (2 ^ (k + 1)) * Z * E ^ (1 - (k : ℝ)) := by ring

/-- **`eq:Ck-growth`** for the constant `(k+2)^{2^{k+1}}`. -/
theorem ck_growth (k : ℕ) : Eq_CkGrowth k (((k : ℝ) + 2) ^ (2 ^ (k + 1))) := by
  refine ⟨by positivity, ?_⟩
  rw [Real.log_pow]
  push_cast
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Real.log_le_log (by positivity) (by have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith)

lemma g_nonneg (e n : ℕ) : 0 ≤ g e n :=
  Finset.sum_nonneg (fun r _ => by positivity)

/-- **`eq:large-count`** from `eq:reflection` and `eq:moment` (lines 628–637), for any `k`, `C_k`. -/
theorem largeCount_of_moment (k : ℕ) (Ck : ℝ) (hR : Eq_Reflection) (hM : Eq_Moment k Ck) :
    Eq_LargeCount k Ck := by
  classical
  intro A X E hA hX hE
  have hAX : 1 ≤ A * X := one_le_mul_of_one_le_of_one_le hA hX
  have hX0 : 0 ≤ X := by linarith
  set M := ⌊A * X⌋₊ with hM_def
  set T : Finset (Σ _ : ℕ, ℕ) := (Icc 1 M).sigma
    (fun n => n.divisors.filter (fun e => E < (e : ℝ) ∧ 1 ≤ A * g e n)) with hT
  have hsub : (Icc 1 ⌊X⌋₊).filter (· ∈ largeCofactorSet A E)
      ⊆ T.image (fun p => F p.2 (p.1 / p.2)) := by
    intro N hN
    rw [Finset.mem_filter] at hN
    obtain ⟨hNI, e, d, he, hd, hNF, hEe, hed⟩ := hN
    have hN1 := Finset.mem_Icc.mp hNI
    have hNX : (N : ℝ) ≤ X := (Nat.cast_le.mpr hN1.2).trans (Nat.floor_le hX0)
    have hed0 : (0 : ℝ) < (e : ℝ) * d := by
      have : (1 : ℝ) ≤ e := by exact_mod_cast he
      have : (1 : ℝ) ≤ d := by exact_mod_cast hd
      nlinarith
    have hrefl := hR e d he hd
    rw [Finset.mem_image]
    refine ⟨⟨e * d, e⟩, ?_, ?_⟩
    · rw [hT, Finset.mem_sigma, Finset.mem_Icc, Finset.mem_filter, Nat.mem_divisors]
      refine ⟨⟨Nat.one_le_iff_ne_zero.mpr (by positivity), Nat.le_floor ?_⟩,
        ⟨dvd_mul_right e d, by positivity⟩, hEe, ?_⟩
      · push_cast
        calc (e : ℝ) * d ≤ A * N := hed
          _ ≤ A * X := mul_le_mul_of_nonneg_left hNX (by linarith)
      · have key : (e : ℝ) * d * 1 ≤ (e : ℝ) * d * (A * g e (e * d)) := by
          rw [mul_one]
          calc (e : ℝ) * d ≤ A * N := hed
            _ = A * (F e d : ℝ) := by rw [hNF]
            _ = (e : ℝ) * d * (A * g e (e * d)) := by rw [hrefl]; ring
        exact le_of_mul_le_mul_left key hed0
    · simp only
      rw [Nat.mul_div_cancel_left d (by omega), hNF]
  have h1 : cnt (largeCofactorSet A E) X ≤ T.card :=
    (Finset.card_le_card hsub).trans Finset.card_image_le
  have h2 : (T.card : ℝ) ≤ A ^ k * momentSum k E (A * X) := by
    rw [hT, Finset.card_sigma, Nat.cast_sum]
    unfold momentSum
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n _
    rw [Finset.mul_sum]
    rw [show n.divisors.filter (fun e : ℕ => E < (e : ℝ) ∧ 1 ≤ A * g e n)
        = (n.divisors.filter (fun e : ℕ => E < (e : ℝ))).filter (fun e : ℕ => 1 ≤ A * g e n) from
        (Finset.filter_filter _ _ _).symm]
    rw [← Finset.sum_boole]
    apply Finset.sum_le_sum
    intro e _
    rw [← mul_pow]
    split_ifs with h
    · exact one_le_pow₀ h
    · exact pow_nonneg (mul_nonneg (by linarith) (g_nonneg e n)) _
  have h3 := hM E (A * X) hE hAX
  calc (cnt (largeCofactorSet A E) X : ℝ) ≤ T.card := by exact_mod_cast h1
    _ ≤ A ^ k * momentSum k E (A * X) := h2
    _ ≤ A ^ k * (Ck * (A * X) * E ^ (1 - (k : ℝ))) :=
        mul_le_mul_of_nonneg_left h3 (pow_nonneg (by linarith) _)
    _ = Ck * A ^ (k + 1) * E ^ (1 - (k : ℝ)) * X := by ring

end Principia.Erdos1054.Proofs.Moment

namespace Principia.Erdos1054.Proofs

open Principia.Erdos1054.Proofs.Moment in
/-- **`lem:moment`** (EP1054.tex lines 565–638), from `eq:reflection`, with the explicit constant
`C_k = (k+2)^{2^{k+1}}` (the paper's `∏_j ζ(1+j/(k+1))^{\binom{k+1}{j}}` is bounded factor by factor
by `k+2`). -/
theorem link_Lem_Moment : Principia.Erdos1054.Spine.Link_Lem_Moment := by
  intro hR k hk
  refine ⟨((k : ℝ) + 2) ^ (2 ^ (k + 1)), ck_growth k, ?_, ?_⟩
  · intro E Z hE hZ
    exact moment_bound k hk E Z hE (by linarith)
  · exact largeCount_of_moment k _ hR (fun E Z hE hZ => moment_bound k hk E Z hE (by linarith))

end Principia.Erdos1054.Proofs
