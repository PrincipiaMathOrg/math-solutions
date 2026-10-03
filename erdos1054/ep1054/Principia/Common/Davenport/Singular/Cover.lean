/-
Copyright (c) 2026 PrincipiaAI. Released under Apache 2.0.
-/
import Principia.Common.Davenport.Concentration
import Principia.Common.Davenport.Singular.SmoothPart
import Principia.Common.Davenport.Singular.Periodic
import Principia.Common.Davenport.Singular.Gap
import Principia.Common.Davenport.Singular.Measure

set_option autoImplicit false

/-!
# The values of `σ(n)/n` concentrate on sets of small Lebesgue measure

**Theorem** (`exists_cover`). For every `0 < ε ≤ 1` there is a finite union `U` of half-open
intervals, of total length `≤ ε`, such that `σ(n)/n ∈ U` for at least `(1 − ε) X` of the
`1 ≤ n ≤ X`, for all large `X`.

**Levels.** `t_i = t₀^{v^i}`, so `t_{i+1} = t_i^v`, and `M_i = ∏_{t_i < p ≤ t_{i+1}} p`. At level
`i` the intervals are `(h_K(a) − s_i, h_K(a) + s_i]`, `1 ≤ a ≤ t_i^u`, `K = t_{i+1}` (`h_K` =
`abundTrunc K`). An `n` lands in one of them as soon as, for some `i`,
(1) `gcd(n, M_i) = 1` (no prime factor in `(t_i, t_{i+1}]`), (2) `smoothPart t_i n ≤ t_i^u`, and
(3) `σ(n)/n − h_K(n) ≤ s_i` — by localisation `h_K(n) = h_K(smoothPart t_i n)`.

**Bad sets.** (A) `gcd(n, M_i) > 1` for all `i < J`: by CRT independence and the gap probability
`∏_{t_i < p ≤ t_i^v} (1 − 1/p) ≥ 1/(2v)`, at most `X (1 − 1/(2v))^J + ∏ M_i ≤ X 2^{-m} + ∏ M_i`;
(B) `smoothPart t_i n > t_i^u` for some `i`: at most `J C_B X / u²` (second moment); (C)
`σ(n)/n − h_K(n) > s_i` for some `i`: at most `∑_i 2X/((K+1)s_i)` (Markov).

**Parameters.** `2^{-m} < ε/4`, `u ≥ 16 m C_B/ε`, `v = u + 1`, `J = 2vm`, `t₀ ≥ 32J²/ε²` (and past
the Mertens threshold of `gap_prod_ge`), `s_i = 8J/(ε(t_{i+1} + 1))`. Then (A), (B), (C) each cost
`≤ εX/4` (plus the fixed `∏ M_i`), and the total length is `∑_i 2 t_i^u s_i ≤ 16J²/(ε t₀) ≤ ε/2`.
-/

namespace Principia.Common.Davenport.Singular

open Finset Filter Principia.Common.Davenport

/-- The level thresholds `t_i = t₀^{v^i}`. -/
def lvl (t₀ v i : ℕ) : ℕ := t₀ ^ (v ^ i)

theorem lvl_succ (t₀ v i : ℕ) : lvl t₀ v (i + 1) = lvl t₀ v i ^ v := by
  unfold lvl
  rw [pow_succ, pow_mul]

theorem lvl_mono {t₀ v : ℕ} (ht₀ : 1 ≤ t₀) (hv : 1 ≤ v) {i j : ℕ} (h : i ≤ j) :
    lvl t₀ v i ≤ lvl t₀ v j :=
  Nat.pow_le_pow_right ht₀ (Nat.pow_le_pow_right hv h)

theorem le_lvl {t₀ v : ℕ} (ht₀ : 1 ≤ t₀) (hv : 1 ≤ v) (i : ℕ) : t₀ ≤ lvl t₀ v i := by
  have h := lvl_mono ht₀ hv (Nat.zero_le i)
  unfold lvl at h ⊢
  simpa using h

/-- The primes of level `i`: `(t_i, t_{i+1}]`. -/
def gapPrimes (t₀ v i : ℕ) : Finset ℕ := (Ioc (lvl t₀ v i) (lvl t₀ v (i + 1))).filter Nat.Prime

/-- `M_i = ∏_{t_i < p ≤ t_{i+1}} p`. -/
def gapMod (t₀ v i : ℕ) : ℕ := ∏ p ∈ gapPrimes t₀ v i, p

theorem gapMod_pos (t₀ v i : ℕ) : 0 < gapMod t₀ v i :=
  Finset.prod_pos fun _ hp => (Finset.mem_filter.1 hp).2.pos

theorem gapMod_coprime {t₀ v : ℕ} (ht₀ : 1 ≤ t₀) (hv : 1 ≤ v) :
    ∀ i j, i ≠ j → Nat.Coprime (gapMod t₀ v i) (gapMod t₀ v j) := by
  have key : ∀ i j, i < j → Nat.Coprime (gapMod t₀ v i) (gapMod t₀ v j) := by
    intro i j hij
    unfold gapMod
    refine Nat.Coprime.prod_left fun p hp => Nat.Coprime.prod_right fun q hq => ?_
    unfold gapPrimes at hp hq
    rw [Finset.mem_filter, Finset.mem_Ioc] at hp hq
    rw [Nat.coprime_primes hp.2 hq.2]
    have h1 : lvl t₀ v (i + 1) ≤ lvl t₀ v j := lvl_mono ht₀ hv (by omega)
    omega
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j h
  · exact (key j i h).symm

/-- Coprimality to `M_i` is the gap `(t_i, t_{i+1}]` in the prime factorisation. -/
theorem gap_of_coprime {t₀ v i n : ℕ} (hc : Nat.Coprime (gapMod t₀ v i) n) :
    ∀ p, p.Prime → p ∣ n → lvl t₀ v i < p → lvl t₀ v (i + 1) < p := by
  intro p hp hpn hlt
  by_contra hle
  push Not at hle
  have hmem : p ∈ gapPrimes t₀ v i := by
    unfold gapPrimes
    rw [Finset.mem_filter, Finset.mem_Ioc]
    exact ⟨⟨hlt, hle⟩, hp⟩
  have hpM : p ∣ gapMod t₀ v i := Finset.dvd_prod_of_mem _ hmem
  have hcp : Nat.Coprime p n := Nat.Coprime.coprime_dvd_left hpM hc
  exact (Nat.Prime.coprime_iff_not_dvd hp).1 hcp hpn

/-- `φ(M_i)/M_i = ∏_{t_i < p ≤ t_{i+1}} (1 − 1/p)`. -/
theorem totient_gapMod (t₀ v i : ℕ) :
    ((gapMod t₀ v i).totient : ℝ) / (gapMod t₀ v i : ℝ) =
      ∏ p ∈ gapPrimes t₀ v i, (1 - 1 / (p : ℝ)) := by
  unfold gapMod
  exact totient_div_prod_eq _ fun p hp => (Finset.mem_filter.1 hp).2

/-- Counting the good `n` from a bad set. -/
theorem countIn_ge_of_bad (f : ℕ → ℝ) (U : Set ℝ) (X : ℕ) (Bad : Finset ℕ)
    (h : ∀ n ∈ Icc 1 X, n ∉ Bad → f n ∈ U) :
    (X : ℝ) - Bad.card ≤ countIn f U X := by
  classical
  unfold countIn
  have hsub : Icc 1 X ⊆ (Icc 1 X).filter (fun n => f n ∈ U) ∪ Bad := by
    intro n hn
    rw [Finset.mem_union, Finset.mem_filter]
    by_cases hb : n ∈ Bad
    · exact Or.inr hb
    · exact Or.inl ⟨hn, h n hn hb⟩
  have h1 := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  rw [Nat.card_Icc, Nat.add_sub_cancel] at h1
  have h2 : (X : ℝ) ≤ (((Icc 1 X).filter (fun n => f n ∈ U)).card : ℝ) + Bad.card := by
    exact_mod_cast h1
  have e : ((Icc 1 X).filter (fun n => f n ∈ U)) =
      (@Finset.filter ℕ (fun n => f n ∈ U) (fun n => Classical.propDecidable _) (Icc 1 X)) := by
    ext n
    simp only [Finset.mem_filter]
  rw [e] at h2
  linarith

/-- `(1 − 1/(2v))^{2v} ≤ 1/2`. -/
theorem one_sub_inv_two_mul_pow_le (v : ℕ) (hv : 1 ≤ v) :
    (1 - 1 / (2 * (v : ℝ))) ^ (2 * v) ≤ 1 / 2 := by
  have hvR : (1 : ℝ) ≤ v := by exact_mod_cast hv
  have hv' : (1 : ℝ) ≤ ((2 * v : ℕ) : ℝ) := by
    push_cast
    linarith
  have h := Real.one_sub_div_pow_le_exp_neg (n := 2 * v) (t := 1) hv'
  push_cast at h
  have he : Real.exp (-1) ≤ 1 / 2 := by
    rw [Real.exp_neg]
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ)
      linarith
    rw [one_div]
    exact inv_anti₀ (by norm_num) h2
  exact h.trans he

/-- One level's contribution to the total length: `T^u · 2s ≤ 16J/(ε t₀)` with
`s = 8J/(ε(T^{u+1} + 1))` and `T ≥ t₀ > 0`. -/
theorem level_length_le (T t₀ J ε : ℝ) (u v : ℕ) (hv : v = u + 1) (hT : t₀ ≤ T) (ht₀ : 0 < t₀)
    (hε : 0 < ε) (hJ : 0 ≤ J) :
    T ^ u * (2 * (8 * J / (ε * (T ^ v + 1)))) ≤ 16 * J / (ε * t₀) := by
  subst hv
  have hTpos : 0 < T := lt_of_lt_of_le ht₀ hT
  have hTu : 0 < T ^ u := pow_pos hTpos u
  have k1 : T ^ u * t₀ ≤ T ^ (u + 1) + 1 := by
    rw [pow_succ]
    have := mul_le_mul_of_nonneg_left hT hTu.le
    linarith
  have k2 := mul_le_mul_of_nonneg_left k1 (show 0 ≤ 16 * J * ε by positivity)
  rw [show T ^ u * (2 * (8 * J / (ε * (T ^ (u + 1) + 1)))) =
      16 * J * T ^ u / (ε * (T ^ (u + 1) + 1)) by ring]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [k2]

/-- **The covering theorem.** -/
theorem exists_cover {ε : ℝ} (hε : 0 < ε) :
    ∃ (S : Finset ((_ : ℕ) × ℕ)) (lo hi : ((_ : ℕ) × ℕ) → ℝ),
      (∀ k ∈ S, lo k ≤ hi k) ∧ (∑ k ∈ S, (hi k - lo k)) ≤ ε ∧
      ∀ᶠ X : ℕ in atTop, (1 - ε) * X ≤ countIn abund (⋃ k ∈ S, Set.Ioc (lo k) (hi k)) X := by
  obtain ⟨t₁, ht₁2, hgap⟩ := gap_prod_ge
  obtain ⟨m, hm⟩ : ∃ m : ℕ, ((1 : ℝ) / 2) ^ m < ε / 4 :=
    exists_pow_lt_of_lt_one (by positivity) (by norm_num)
  have hCB := tailConst_pos
  set u : ℕ := ⌈16 * m * tailConst / ε⌉₊ + 1 with hudef
  have hu1 : 1 ≤ u := by omega
  have huR : 16 * m * tailConst / ε ≤ (u : ℝ) := by
    have := Nat.le_ceil (16 * m * tailConst / ε)
    rw [hudef]
    push_cast
    linarith
  set v : ℕ := u + 1 with hvdef
  have hv1 : 1 ≤ v := by omega
  set J : ℕ := 2 * v * m with hJdef
  set t₀ : ℕ := max t₁ ⌈32 * (J : ℝ) ^ 2 / ε ^ 2⌉₊ with ht₀def
  have ht₀1 : t₁ ≤ t₀ := le_max_left _ _
  have ht₀2 : 2 ≤ t₀ := le_trans ht₁2 ht₀1
  have ht₀R : 32 * (J : ℝ) ^ 2 / ε ^ 2 ≤ t₀ := by
    have h1 := Nat.le_ceil (32 * (J : ℝ) ^ 2 / ε ^ 2)
    have h2 : ⌈32 * (J : ℝ) ^ 2 / ε ^ 2⌉₊ ≤ t₀ := le_max_right _ _
    have h3 : ((⌈32 * (J : ℝ) ^ 2 / ε ^ 2⌉₊ : ℕ) : ℝ) ≤ (t₀ : ℝ) := by exact_mod_cast h2
    linarith
  set t : ℕ → ℕ := lvl t₀ v with htdef
  have ht2 : ∀ i, 2 ≤ t i := fun i => le_trans ht₀2 (le_lvl (by omega) hv1 i)
  have htt₀ : ∀ i, t₀ ≤ t i := fun i => le_lvl (by omega) hv1 i
  have htsucc : ∀ i, t (i + 1) = t i ^ v := fun i => lvl_succ t₀ v i
  set s : ℕ → ℝ := fun i => 8 * J / (ε * ((t (i + 1) : ℝ) + 1)) with hsdef
  have hs0 : ∀ i, 0 ≤ s i := fun i => by
    simp only [hsdef]
    positivity
  set S : Finset ((_ : ℕ) × ℕ) := (range J).sigma (fun i => Icc 1 (t i ^ u)) with hSdef
  set lo : ((_ : ℕ) × ℕ) → ℝ := fun k => abundTrunc (t (k.1 + 1)) k.2 - s k.1 with hlodef
  set hi : ((_ : ℕ) × ℕ) → ℝ := fun k => abundTrunc (t (k.1 + 1)) k.2 + s k.1 with hhidef
  refine ⟨S, lo, hi, ?_, ?_, ?_⟩
  -- the intervals are genuine
  · intro k _
    simp only [hlodef, hhidef]
    linarith [hs0 k.1]
  -- total length
  · have hlen : ∑ k ∈ S, (hi k - lo k) = ∑ i ∈ range J, ((t i ^ u : ℕ) : ℝ) * (2 * s i) := by
      rw [hSdef, Finset.sum_sigma]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hc : ∀ x ∈ Icc 1 (t i ^ u), hi ⟨i, x⟩ - lo ⟨i, x⟩ = 2 * s i := fun x _ => by
        simp only [hlodef, hhidef]
        ring
      rw [Finset.sum_congr rfl hc, Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel,
        nsmul_eq_mul]
    rw [hlen]
    have hJε : (J : ℝ) * (16 * J / (ε * t₀)) ≤ ε := by
      have ht₀pos : (0 : ℝ) < t₀ := by exact_mod_cast (show 0 < t₀ by omega)
      have h32 : 32 * (J : ℝ) ^ 2 ≤ ε ^ 2 * t₀ := by
        rw [div_le_iff₀ (by positivity)] at ht₀R
        linarith
      rw [show (J : ℝ) * (16 * J / (ε * t₀)) = 16 * (J : ℝ) ^ 2 / (ε * t₀) by ring,
        div_le_iff₀ (by positivity)]
      nlinarith
    calc ∑ i ∈ range J, ((t i ^ u : ℕ) : ℝ) * (2 * s i)
        ≤ ∑ _i ∈ range J, 16 * (J : ℝ) / (ε * t₀) := by
          refine Finset.sum_le_sum fun i _ => ?_
          have hTt₀ : (t₀ : ℝ) ≤ t i := by exact_mod_cast htt₀ i
          have ht₀pos : (0 : ℝ) < t₀ := by exact_mod_cast (show 0 < t₀ by omega)
          simp only [hsdef]
          rw [htsucc i]
          push_cast
          exact level_length_le (t i : ℝ) t₀ J ε u v hvdef hTt₀ ht₀pos hε (Nat.cast_nonneg J)
      _ = (J : ℝ) * (16 * J / (ε * t₀)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ ε := hJε
  -- the count
  · set M : ℕ → ℕ := gapMod t₀ v with hMdef
    set N : ℕ := ∏ i ∈ range J, M i with hNdef
    filter_upwards [eventually_ge_atTop ⌈4 * (N : ℝ) / ε⌉₊] with X hX
    have hXN : 4 * (N : ℝ) / ε ≤ X := le_trans (Nat.le_ceil _) (by exact_mod_cast hX)
    have hNX : (N : ℝ) ≤ ε * X / 4 := by
      rw [div_le_iff₀ hε] at hXN
      linarith
    have hX0 : (0 : ℝ) ≤ X := Nat.cast_nonneg X
    -- the bad sets
    set A : Finset ℕ := (Icc 1 X).filter (fun n => ∀ i < J, ¬ Nat.Coprime (M i) n) with hAdef
    set B : ℕ → Finset ℕ := fun i => (Icc 1 X).filter (fun n => t i ^ u < smoothPart (t i) n)
      with hBdef
    set C : ℕ → Finset ℕ := fun i =>
      (Icc 1 X).filter (fun n => s i < abund n - abundTrunc (t (i + 1)) n) with hCdef
    set Bad : Finset ℕ := A ∪ (range J).biUnion B ∪ (range J).biUnion C with hBaddef
    -- (A)
    have hWi : ∀ i, (1 : ℝ) / (2 * v) ≤ ∏ p ∈ gapPrimes t₀ v i, (1 - 1 / (p : ℝ)) := by
      intro i
      have h := hgap (t i) v (le_trans ht₀1 (htt₀ i)) hv1
      unfold gapPrimes
      rw [show lvl t₀ v (i + 1) = t i ^ v from htsucc i]
      exact h
    have hWle : ∀ i, ∏ p ∈ gapPrimes t₀ v i, (1 - 1 / (p : ℝ)) ≤ 1 := by
      intro i
      refine Finset.prod_le_one (fun p hp => ?_) (fun p hp => ?_)
      · have hpp := (Finset.mem_filter.1 hp).2
        have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
        have : (1 : ℝ) / p ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) h2
        linarith
      · have hpp := (Finset.mem_filter.1 hp).2
        have : (0 : ℝ) ≤ 1 / p := by positivity
        linarith
    have hprod : ∏ i ∈ range J, (1 - (Nat.totient (M i) : ℝ) / M i) ≤ ε / 4 := by
      calc ∏ i ∈ range J, (1 - (Nat.totient (M i) : ℝ) / M i)
          ≤ ∏ _i ∈ range J, (1 - 1 / (2 * (v : ℝ))) := by
            refine Finset.prod_le_prod (fun i _ => ?_) (fun i _ => ?_)
            · rw [hMdef, totient_gapMod]
              linarith [hWle i]
            · rw [hMdef, totient_gapMod]
              linarith [hWi i]
        _ = ((1 - 1 / (2 * (v : ℝ))) ^ (2 * v)) ^ m := by
            rw [Finset.prod_const, Finset.card_range, hJdef, pow_mul]
        _ ≤ (1 / 2) ^ m := by
            apply pow_le_pow_left₀ _ (one_sub_inv_two_mul_pow_le v hv1)
            have hvR : (1 : ℝ) ≤ v := by exact_mod_cast hv1
            have h1 : 1 / (2 * (v : ℝ)) ≤ 1 := by
              rw [div_le_one (by positivity)]
              linarith
            exact pow_nonneg (by linarith) _
        _ ≤ ε / 4 := hm.le
    have hA : (A.card : ℝ) ≤ ε * X / 4 + ε * X / 4 := by
      have h := card_Icc_forall_not_coprime_le M (gapMod_pos t₀ v)
        (gapMod_coprime (by omega) hv1) J X
      have h' : (X : ℝ) * ∏ i ∈ range J, (1 - (Nat.totient (M i) : ℝ) / M i) ≤ X * (ε / 4) :=
        mul_le_mul_of_nonneg_left hprod hX0
      have hNR : ∏ i ∈ range J, (M i : ℝ) = N := by rw [hNdef, Nat.cast_prod]
      rw [hNR] at h
      linarith
    -- (B)
    have hB : (((range J).biUnion B).card : ℝ) ≤ ε * X / 4 := by
      have h1 : (((range J).biUnion B).card : ℝ) ≤ ∑ i ∈ range J, ((B i).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
      have h2 : ∀ i ∈ range J, ((B i).card : ℝ) ≤ tailConst * X / (u : ℝ) ^ 2 :=
        fun i _ => card_smoothPart_gt_le (t i) X u (ht2 i) (by omega)
      have h3 := Finset.sum_le_sum h2
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h3
      have huR0 : (0 : ℝ) < u := by exact_mod_cast (show 0 < u by omega)
      have hJu : (J : ℝ) ≤ 4 * u * m := by
        rw [hJdef, hvdef]
        push_cast
        have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
        have hu1R : (1 : ℝ) ≤ u := by exact_mod_cast hu1
        nlinarith
      have key : (J : ℝ) * (tailConst * X / (u : ℝ) ^ 2) ≤ ε * X / 4 := by
        have e1 : (J : ℝ) * (tailConst * X / (u : ℝ) ^ 2) ≤
            4 * u * m * (tailConst * X / (u : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right hJu (by positivity)
        have e2 : 4 * (u : ℝ) * m * (tailConst * X / (u : ℝ) ^ 2) =
            (4 * m * tailConst / u) * X := by
          field_simp
        have e3 : 4 * (m : ℝ) * tailConst / u ≤ ε / 4 := by
          rw [div_le_iff₀ huR0]
          rw [div_le_iff₀ hε] at huR
          linarith
        have e4 := mul_le_mul_of_nonneg_right e3 hX0
        linarith
      linarith
    -- (C)
    have hC : (((range J).biUnion C).card : ℝ) ≤ ε * X / 4 := by
      have h1 : (((range J).biUnion C).card : ℝ) ≤ ∑ i ∈ range J, ((C i).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
      have h2 : ∀ i ∈ range J, ((C i).card : ℝ) ≤ ε * X / (4 * J) := by
        intro i hi
        have hJ0 : 0 < J := by
          rw [Finset.mem_range] at hi
          omega
        have hJR : (0 : ℝ) < J := by exact_mod_cast hJ0
        have hK : (0 : ℝ) < (t (i + 1) : ℝ) + 1 := by positivity
        have hspos : 0 < s i := by
          simp only [hsdef]
          positivity
        have h := card_tail_gt_le (t (i + 1)) X hspos
        have e : (X : ℝ) * (2 / ((t (i + 1) : ℕ) + 1)) / s i = ε * X / (4 * J) := by
          simp only [hsdef]
          field_simp
          ring
        simp only [hCdef]
        rw [← e]
        exact h
      have h3 := Finset.sum_le_sum h2
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h3
      rcases Nat.eq_zero_or_pos J with hJ | hJ
      · rw [hJ, Finset.range_zero, Finset.biUnion_empty, Finset.card_empty, Nat.cast_zero]
        positivity
      · have hJR : (0 : ℝ) < J := by exact_mod_cast hJ
        have e : (J : ℝ) * (ε * X / (4 * J)) = ε * X / 4 := by field_simp
        linarith
    have hBad : (Bad.card : ℝ) ≤ ε * X := by
      have h1 : (Bad.card : ℝ) ≤ A.card + ((range J).biUnion B).card +
          ((range J).biUnion C).card := by
        have := (Finset.card_union_le (A ∪ (range J).biUnion B) ((range J).biUnion C)).trans
          (Nat.add_le_add_right (Finset.card_union_le A ((range J).biUnion B)) _)
        exact_mod_cast this
      linarith
    -- every good `n` is covered
    have hgood : ∀ n ∈ Icc 1 X, n ∉ Bad → abund n ∈ ⋃ k ∈ S, Set.Ioc (lo k) (hi k) := by
      intro n hn hnBad
      have hn1 : 1 ≤ n := (Finset.mem_Icc.1 hn).1
      rw [hBaddef, Finset.mem_union, Finset.mem_union, not_or, not_or] at hnBad
      obtain ⟨⟨hnA, hnB⟩, hnC⟩ := hnBad
      have hex : ∃ i < J, Nat.Coprime (M i) n := by
        by_contra hcon
        push Not at hcon
        exact hnA (Finset.mem_filter.2 ⟨hn, hcon⟩)
      obtain ⟨i, hiJ, hcop⟩ := hex
      have hiJ' : i ∈ range J := Finset.mem_range.2 hiJ
      have hnBi : ¬ t i ^ u < smoothPart (t i) n := by
        intro h
        exact hnB (Finset.mem_biUnion.2 ⟨i, hiJ', Finset.mem_filter.2 ⟨hn, h⟩⟩)
      have hnCi : ¬ s i < abund n - abundTrunc (t (i + 1)) n := by
        intro h
        exact hnC (Finset.mem_biUnion.2 ⟨i, hiJ', Finset.mem_filter.2 ⟨hn, h⟩⟩)
      push Not at hnBi hnCi
      set a := smoothPart (t i) n with hadef
      have ha1 : 1 ≤ a := Nat.one_le_iff_ne_zero.2 (smoothPart_ne_zero _ _)
      have hloc : abundTrunc (t (i + 1)) n = abundTrunc (t (i + 1)) a :=
        abundTrunc_eq_smoothPart (t i) (t (i + 1)) (by omega) (gap_of_coprime hcop)
      have hspos : 0 < s i := by
        have hJ0 : 0 < J := by omega
        simp only [hsdef]
        positivity
      have hle := abundTrunc_le_abund (t (i + 1)) n (by omega)
      refine Set.mem_iUnion₂.2 ⟨⟨i, a⟩, ?_, ?_⟩
      · rw [hSdef, Finset.mem_sigma]
        exact ⟨hiJ', Finset.mem_Icc.2 ⟨ha1, hnBi⟩⟩
      · simp only [hlodef, hhidef, Set.mem_Ioc]
        rw [← hloc]
        constructor <;> linarith
    have hcount := countIn_ge_of_bad abund (⋃ k ∈ S, Set.Ioc (lo k) (hi k)) X Bad hgood
    have : (1 - ε) * (X : ℝ) = X - ε * X := by ring
    linarith

end Principia.Common.Davenport.Singular
